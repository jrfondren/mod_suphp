/*
  suPHP - (c)2002-2013 Sebastian Marsching <sebastian@marsching.com>
          (c)2018 John Lightsey <john@nixnuts.net>
          (c)2019 Julian Fondren <julian.fondren@endurance.com>

  This file is part of suPHP.

  suPHP is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  suPHP is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with suPHP; if not, write to the Free Software Foundation, Inc.,
  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
*/

#include "apr.h"
#include "apr_buckets.h"
#include "apr_poll.h"
#include "apr_strings.h"
#include "apr_thread_proc.h"
#include "apr_signal.h"
#include "apr_portable.h"
#include "apr_lib.h"

#if APR_HAVE_USER
#include "apr_user.h"
#endif

#ifndef OPT_APACHE_USER
#define OPT_APACHE_USER "apache"
#endif

#if APR_HAVE_SYS_SOCKET_H
#include <sys/socket.h>
#endif
#if APR_HAVE_UNISTD_H
#include <unistd.h>
#endif
#if APR_HAVE_SYS_TYPES_H
#include <sys/types.h>
#endif

#define CORE_PRIVATE

#include "httpd.h"

#include "http_config.h"
#include "http_core.h"
#include "http_log.h"

#if HTTP_VERSION(AP_SERVER_MAJORVERSION_NUMBER, AP_SERVER_MINORVERSION_NUMBER) >= 2002
#include "http_request.h"
#endif

#include "util_filter.h"
#include "util_script.h"
#include "ap_mpm.h"

/* needed for get_suexec_identity hook */
#include "unixd.h"
#include "mod_unixd.h"

/* ### should be tossed in favor of APR */
#include <sys/stat.h>
#include <sys/un.h> /* for sockaddr_un */


module AP_MODULE_DECLARE_DATA suphpd_module;

static int suphpd_start(apr_pool_t *p, server_rec *main_server, apr_proc_t *procnew);
static int suphpd_init(apr_pool_t *p, apr_pool_t *plog, apr_pool_t *ptemp, server_rec *main_server);
static void suphpd_maint(int reason, void *data, apr_wait_t status);

static apr_pool_t *pcgi = NULL;
static pid_t daemon_pid;
static int daemon_should_exit = 0;
static server_rec *root_server = NULL;
static apr_pool_t *root_pool = NULL;
static const char *sockname;
static apr_uid_t sockuid;
static apr_gid_t sockgid;
static pid_t parent_pid;

/* The APR other-child API doesn't tell us how the daemon exited
 * (SIGSEGV vs. exit(1)).  The other-child maintenance function
 * needs to decide whether to restart the daemon after a failure
 * based on whether or not it exited due to a fatal startup error
 * or something that happened at steady-state.  This exit status
 * is unlikely to collide with exit signals.
 */
#define DAEMON_STARTUP_ERROR 254

#define DEFAULT_SOCKET  DEFAULT_REL_RUNTIMEDIR "/suphpdsock"

#define PHP_REQ    1
#define SRC_REQ    2 /* run php -s instead of suphp */
#define GETPID_REQ 3 /* get the pid of script created for prior request */

#define ERRFN_USERDATA_KEY         "SUPHPDCHILDERRFN"

/* DEFAULT_CGID_LISTENBACKLOG controls the max depth on the unix socket's
 * pending connection queue.  If a bunch of cgi requests arrive at about
 * the same time, connections from httpd threads/processes will back up
 * in the queue while the cgid process slowly forks off a child to process
 * each connection on the unix socket.  If the queue is too short, the
 * httpd process will get ECONNREFUSED when trying to connect.
 */
#ifndef DEFAULT_SUPHPD_LISTENBACKLOG
#define DEFAULT_SUPHPD_LISTENBACKLOG 100
#endif

/* DEFAULT_CONNECT_ATTEMPTS controls how many times we'll try to connect
 * to the cgi daemon from the thread/process handling the cgi request.
 * Generally we want to retry when we get ECONNREFUSED since it is
 * probably because the listen queue is full.  We need to try harder so
 * the client doesn't see it as a 503 error.
 *
 * Set this to 0 to continually retry until the connect works or Apache
 * terminates.
 */
#ifndef DEFAULT_CONNECT_ATTEMPTS
#define DEFAULT_CONNECT_ATTEMPTS  15
#endif

/******************
  Socket functions
 ******************/

typedef struct {
  int req_type; /* request type (PHP_REQ, SRC_REQ, etc.) */
  unsigned long conn_id; /* connection id; daemon uses this as a hash value
                          * to find the script pid when it is time for that
                          * process to be cleaned up
                          */
  pid_t ppid;            /* sanity check for config problems leading to
                          * wrong cgid socket use
                          */
  apr_size_t filename_len;
  apr_size_t uri_len;
  int env_count;
} suphpd_req_t;

/* deal with incomplete reads and signals
 * assume you really have to read buf_size bytes
 */
static apr_status_t sock_read(int fd, void *vbuf, size_t buf_size) {
  char *buf = vbuf;
  int rc;
  size_t bytes_read = 0;

  do {
    do {
      rc = read(fd, buf + bytes_read, buf_size - bytes_read);
    } while (rc < 0 && errno == EINTR);
    switch(rc) {
    case -1:
      return errno;
    case 0: /* unexpected */
      return ECONNRESET;
    default:
      bytes_read += rc;
    }
  } while (bytes_read < buf_size);

  return APR_SUCCESS;
}

/* deal with signals
 */
static apr_status_t sock_write(int fd, const void *buf, size_t buf_size) {
  int rc;

  do {
    rc = write(fd, buf, buf_size);
  } while (rc < 0 && errno == EINTR);
  if (rc < 0) {
    return errno;
  }

  return APR_SUCCESS;
}

static apr_status_t send_req(int fd, request_rec *r, char **env, int req_type) {
  int i;
  suphpd_req_t req;
  apr_status_t stat;

  req.req_type = req_type;
  req.conn_id = r->connection->id;
  req.ppid = parent_pid;
  if (req_type != GETPID_REQ) {
    req.filename_len = strlen(r->filename);
    req.uri_len = strlen(r->uri);
    for (req.env_count = 0; env[req.env_count]; req.env_count++);
  }

  /* write the request header */
  stat = sock_write(fd, &req, sizeof(req));
  if (stat != APR_SUCCESS) return stat;
  if (req_type == GETPID_REQ) return APR_SUCCESS;

  stat = sock_write(fd, r->filename, req.filename_len);
  if (stat != APR_SUCCESS) return stat;
  stat = sock_write(fd, r->uri, req.uri_len);
  if (stat != APR_SUCCESS) return stat;

  /* write the environment variables */
  for (i = 0; i < req.env_count; i++) {
    apr_size_t curlen = strlen(env[i]);

    if (APR_SUCCESS != (stat = sock_write(fd, &curlen, sizeof(curlen)))) return stat;
    if (APR_SUCCESS != (stat = sock_write(fd, env[i], curlen))) return stat;
  }

  return APR_SUCCESS;
}

/* --> request_rec is fake <--
 * incoming: needs valid r->pool
 * outgoing (if not GETPID_REQ): will have valid r->filename and r->uri
 * no other fields should be used and request_rec shouldn't be reused.
 *
 * mod_cgid passes its fake request_rec to functions outside its code base;
 * we can't duplicate that because these functions depend on r->server, which
 * is an opaque type for us.
 */
static apr_status_t get_req(int fd, request_rec *r, char ***env, suphpd_req_t *req) {
  int i;
  apr_status_t stat;
  char **environ;

  /* read the request header */
  stat = sock_read(fd, req, sizeof(*req));
  if (stat != APR_SUCCESS) return stat;
  if (req->req_type == GETPID_REQ) return APR_SUCCESS;

  r->filename = apr_pcalloc(r->pool, req->filename_len + 1);
  stat = sock_read(fd, r->filename, req->filename_len);
  if (stat != APR_SUCCESS) return stat;
  r->uri = apr_pcalloc(r->pool, req->uri_len + 1);
  stat = sock_read(fd, r->uri, req->uri_len);
  if (stat != APR_SUCCESS) return stat;

  /* read the environment variables */
  environ = apr_pcalloc(r->pool, (req->env_count + 2) * sizeof(char *));
  for (i = 0; i < req->env_count; i++) {
    apr_size_t curlen;

    if ((stat = sock_read(fd, &curlen, sizeof(curlen))) != APR_SUCCESS) {
      return stat;
    }
    environ[i] = apr_pcalloc(r->pool, curlen + 1);
    if ((stat = sock_read(fd, environ[i], curlen)) != APR_SUCCESS) {
      return stat;
    }
  }
  *env = environ;

  return APR_SUCCESS;
}

/******************
  Daemon functions
 ******************/

static apr_status_t close_unix_socket(void *thefd) {
  int fd = (int)((long)thefd);

  return close(fd);
}

static int connect_to_daemon(int *sdptr, request_rec *r) {
  struct sockaddr_un unix_addr;
  int sd;
  int connect_tries;
  apr_interval_time_t sliding_timer;

  memset(&unix_addr, 0, sizeof(unix_addr));
  unix_addr.sun_family = AF_UNIX;
  apr_cpystrn(unix_addr.sun_path, sockname, sizeof unix_addr.sun_path);

  connect_tries = 0;
  sliding_timer = 100000; /* 100 milliseconds */
  while (1) {
      ++connect_tries;
      if ((sd = socket(AF_UNIX, SOCK_STREAM, 0)) < 0) {
          ap_log_error(APLOG_MARK, APLOG_ERR, HTTP_INTERNAL_SERVER_ERROR, r->server,
                       "unable to create socket to suphp daemon");
          return DECLINED;
      }
      if (connect(sd, (struct sockaddr *)&unix_addr, sizeof(unix_addr)) < 0) {
          if (errno == ECONNREFUSED && connect_tries < DEFAULT_CONNECT_ATTEMPTS) {
              ap_log_rerror(APLOG_MARK, APLOG_DEBUG, errno, r,
                            "connect #%d to suphp daemon failed, sleeping before retry",
                            connect_tries);
              close(sd);
              apr_sleep(sliding_timer);
              if (sliding_timer < apr_time_from_sec(2)) {
                  sliding_timer *= 2;
              }
          }
          else {
              close(sd);
              ap_log_error(APLOG_MARK, APLOG_ERR, HTTP_SERVICE_UNAVAILABLE, r->server,
                          "unable to connect to suphp daemon after multiple tries");
          }
      }
      else {
          apr_pool_cleanup_register(r->pool, (void *)((long)sd),
                                    close_unix_socket, apr_pool_cleanup_null);
          break; /* we got connected! */
      }
      /* gotta try again, but make sure the cgid daemon is still around */
      if (kill(daemon_pid, 0) != 0) {
          ap_log_error(APLOG_MARK, APLOG_ERR, HTTP_SERVICE_UNAVAILABLE, r->server,
                      "suphp daemon is gone; is Apache terminating?");
          return DECLINED;
      }
  }
  *sdptr = sd;
  return OK;
}

static void daemon_signal_handler(int sig) {
  if (sig == SIGHUP) {
    ++daemon_should_exit;
  }
}
static void suphpd_child_errfn(apr_pool_t *pool, apr_status_t err,
                             const char *description) {
  request_rec *r;
  void *vr;

  apr_pool_userdata_get(&vr, ERRFN_USERDATA_KEY, pool);
  r = vr;

  /* sure we got r, but don't call ap_log_rerror() because we don't
    * have r->headers_in and possibly other storage referenced by
    * ap_log_rerror()
    */
  ap_log_error(APLOG_MARK, APLOG_ERR, err, r->server, "%s", description);
}

/* This doer will only ever be called when we are sure that we have
 * a valid ugid.
 */
static ap_unix_identity_t *suphpd_suexec_id_doer(const request_rec *r)
{
    return (ap_unix_identity_t *)
                        ap_get_module_config(r->request_config, &suphpd_module);
}

static int suphpd_server(void *data)
{
    struct sockaddr_un unix_addr;
    int sd, sd2, rc;
    mode_t omask;
    apr_socklen_t len;
    apr_pool_t *ptrans;
    server_rec *main_server = data;
    apr_hash_t *script_hash = apr_hash_make(pcgi);
    apr_status_t rv;

    apr_pool_create(&ptrans, pcgi);

    apr_signal(SIGCHLD, SIG_IGN);
    apr_signal(SIGHUP, daemon_signal_handler);

    /* Close our copy of the listening sockets */
    ap_close_listeners();

    /* cgid should use its own suexec doer */
    ap_hook_get_suexec_identity(suphpd_suexec_id_doer, NULL, NULL,
                                APR_HOOK_REALLY_FIRST);
    apr_hook_sort_all();

    if ((sd = socket(AF_UNIX, SOCK_STREAM, 0)) < 0) {
        ap_log_error(APLOG_MARK, APLOG_ERR, errno, main_server,
                     "Couldn't create unix domain socket");
        return errno;
    }

    memset(&unix_addr, 0, sizeof(unix_addr));
    unix_addr.sun_family = AF_UNIX;
    apr_cpystrn(unix_addr.sun_path, sockname, sizeof unix_addr.sun_path);

    omask = umask(0077); /* so that only Apache can use socket */
    rc = bind(sd, (struct sockaddr *)&unix_addr, sizeof(unix_addr));
    umask(omask); /* can't fail, so can't clobber errno */
    if (rc < 0) {
        ap_log_error(APLOG_MARK, APLOG_ERR, errno, main_server,
                     "Couldn't bind unix domain socket %s",
                     sockname);
        return errno;
    }

    /* Not all flavors of unix use the current umask for AF_UNIX perms */
    rv = apr_file_perms_set(sockname, APR_FPROT_UREAD|APR_FPROT_UWRITE|APR_FPROT_UEXECUTE);
    if (rv != APR_SUCCESS) {
        ap_log_error(APLOG_MARK, APLOG_CRIT, rv, main_server,
                     "Couldn't set permissions on unix domain socket %s",
                     sockname);
        return rv;
    }

    if (listen(sd, DEFAULT_SUPHPD_LISTENBACKLOG) < 0) {
        ap_log_error(APLOG_MARK, APLOG_ERR, errno, main_server,
                     "Couldn't listen on unix domain socket");
        return errno;
    }

    if (!geteuid()) {
        if (chown(sockname, sockuid, -1) < 0) {
            ap_log_error(APLOG_MARK, APLOG_ERR, errno, main_server,
                         "Couldn't change owner of unix domain socket %s",
                         sockname);
            return errno;
        }
    }

    ap_unixd_setup_child(); /* if running as root, switch to configured user/group */

    while (!daemon_should_exit) {
        int errfileno = STDERR_FILENO;
        char **env = NULL;
        request_rec *fake_r; /* see get_req() comments */
        char **argv;
        apr_procattr_t *procattr = NULL;
        apr_proc_t *procnew = NULL;
        apr_file_t *inout;
        apr_file_t *errfile;
        suphpd_req_t suphpd_req;
        apr_status_t stat;

        apr_pool_clear(ptrans);

        len = sizeof(unix_addr);
        sd2 = accept(sd, (struct sockaddr *)&unix_addr, &len);
        if (sd2 < 0) {
#if defined(ENETDOWN)
            if (errno == ENETDOWN) {
                /* The network has been shut down, no need to continue. Die gracefully */
                ++daemon_should_exit;
            }
#endif
            if (errno != EINTR) {
                ap_log_error(APLOG_MARK, APLOG_ERR, errno,
                             (server_rec *)data,
                             "Error accepting on suphpd socket");
            }
            continue;
        }

        fake_r = apr_pcalloc(ptrans, sizeof(request_rec));
        fake_r->pool = ptrans;
        stat = get_req(sd2, fake_r, &env, &suphpd_req);
        if (stat != APR_SUCCESS) {
            ap_log_error(APLOG_MARK, APLOG_ERR, stat,
                         main_server,
                         "Error reading request on suphpd socket");
            close(sd2);
            continue;
        }

        if (suphpd_req.ppid != parent_pid) {
            ap_log_error(APLOG_MARK, APLOG_CRIT, 0, main_server,
                         "CGI request received from wrong server instance; "
                         "see ScriptSock directive");
            close(sd2);
            continue;
        }

        if (suphpd_req.req_type == GETPID_REQ) {
            pid_t pid;

            pid = (pid_t)((long)apr_hash_get(script_hash, &suphpd_req.conn_id, sizeof(suphpd_req.conn_id)));
            if (write(sd2, &pid, sizeof(pid)) != sizeof(pid)) {
                ap_log_error(APLOG_MARK, APLOG_ERR, 0,
                             main_server,
                             "Error writing pid %" APR_PID_T_FMT " to handler", pid);
            }
            close(sd2);
            continue;
        }

        apr_os_file_put(&errfile, &errfileno, 0, fake_r->pool);
        apr_os_file_put(&inout, &sd2, 0, fake_r->pool);

        /* in:          rc = call1() != APR_SUCCESS;
         *              rc |= call2() != APR_SUCCESS;
         *              rc |= call3() != APR_SUCCESS;
         *              ...
         *
         * rc is initally assigned to 0 (or 1 if call1() != APR_SUCCESS)
         * the final value of rc will be 0 (or 1 if any call#() != APR_SUCCESS)
         */
        rc = apr_procattr_create(&procattr, ptrans) != APR_SUCCESS;
        rc |= apr_procattr_io_set(procattr,
                                  APR_CHILD_BLOCK,
                                  APR_CHILD_BLOCK,
                                  APR_CHILD_BLOCK) != APR_SUCCESS;
        /* XXX apr_procattr_child_*_set() is creating an unnecessary
         * pipe between this process and the child being created...
         * It is cleaned up with the temporary pool for this request.
         */
        rc |= apr_procattr_child_err_set(procattr, errfile, NULL) != APR_SUCCESS;
        rc |= apr_procattr_child_in_set(procattr, inout, NULL) != APR_SUCCESS;
        rc |= apr_procattr_child_out_set(procattr, inout, NULL) != APR_SUCCESS;
        rc |= apr_procattr_dir_set(procattr,
                                   ap_make_dirstr_parent(fake_r->pool, fake_r->filename))
                                   != APR_SUCCESS;
// XXX disable until core_conf fields can be available to server
#if 0
#ifdef RLIMIT_CPU
        rc |= apr_procattr_limit_set(procattr, APR_LIMIT_CPU,
                                     core_conf->limit_cpu) != APR_SUCCESS;
#endif
#if defined(RLIMIT_DATA) || defined(RLIMIT_VMEM) || defined(RLIMIT_AS)
        rc |= apr_procattr_limit_set(procattr, APR_LIMIT_MEM,
                                     core_conf->limit_mem) != APR_SUCCESS;
#endif
#ifdef RLIMIT_NPROC
        rc |= apr_procattr_limit_set(procattr, APR_LIMIT_NPROC,
                                     core_conf->limit_nproc) != APR_SUCCESS;
#endif
#endif
        rc |= apr_procattr_cmdtype_set(procattr, APR_PROGRAM) != APR_SUCCESS;
        rc |= apr_procattr_error_check_set(procattr, 1) != APR_SUCCESS;
        rc |= apr_procattr_detach_set(procattr, 0) != APR_SUCCESS;
        rc |= apr_procattr_child_errfn_set(procattr, suphpd_child_errfn) != APR_SUCCESS;
        if (rc) {
            /* Something bad happened, tell the world.
             * ap_log_rerror() won't work because the header table used by
             * ap_log_rerror() hasn't been replicated in the phony r
             */
            ap_log_error(APLOG_MARK, APLOG_ERR, rc, main_server,
                         "couldn't set child process attributes: %s", fake_r->filename);
        }
        else {
            apr_pool_userdata_set(fake_r, ERRFN_USERDATA_KEY, apr_pool_cleanup_null, ptrans);

           /* We want to close sd2 for the new CGI process too.
            * If it is left open it'll make ap_pass_brigade() block
            * waiting for EOF if CGI forked something running long.
            * close(sd2) here should be okay, as CGI channel
            * is already dup()ed by apr_procattr_child_{in,out}_set()
            * above.
            */
            close(sd2);

            argv = apr_pcalloc(ptrans, 2 * sizeof(char *));
            argv[0] = SUPHP_PATH_TO_SUPHP;
            argv[1] = NULL;

            procnew = apr_pcalloc(ptrans, sizeof(*procnew));
            rc = apr_proc_create(procnew, SUPHP_PATH_TO_SUPHP, (const char * const *)argv,
                                 (const char * const *)env,
                                 procattr, ptrans);

            if (rc != APR_SUCCESS) {
                /* Bad things happened. Everyone should have cleaned up.
                 * ap_log_rerror() won't work because the header table used by
                 * ap_log_rerror() hasn't been replicated in the phony r
                 */
                ap_log_error(APLOG_MARK, APLOG_ERR, rc, main_server,
                             "couldn't create child process: %d: %s", rc,
                             apr_filepath_name_get(fake_r->filename));
            }
            else {
                /* We don't want to leak storage for the key, so only allocate
                 * a key if the key doesn't exist yet in the hash; there are
                 * only a limited number of possible keys (one for each
                 * possible thread in the server), so we can allocate a copy
                 * of the key the first time a thread has a cgid request.
                 * Note that apr_hash_set() only uses the storage passed in
                 * for the key if it is adding the key to the hash for the
                 * first time; new key storage isn't needed for replacing the
                 * existing value of a key.
                 */
                void *key;

                if (apr_hash_get(script_hash, &suphpd_req.conn_id, sizeof(suphpd_req.conn_id))) {
                    key = &suphpd_req.conn_id;
                }
                else {
                    key = apr_pcalloc(pcgi, sizeof(suphpd_req.conn_id));
                    memcpy(key, &suphpd_req.conn_id, sizeof(suphpd_req.conn_id));
                }
                apr_hash_set(script_hash, key, sizeof(suphpd_req.conn_id),
                             (void *)((long)procnew->pid));

// XXX: subprocess killed too soon
//                apr_pool_note_subprocess(ptrans, procnew, APR_KILL_AFTER_TIMEOUT);
//
//                if (procnew->out) apr_file_pipe_timeout_set(procnew->out, main_server->timeout);
//
//                if (procnew->in) apr_file_pipe_timeout_set(procnew->in, main_server->timeout);
//
//                if (procnew->err) apr_file_pipe_timeout_set(procnew->err, main_server->timeout);
            }
        }
    }
    return -1; /* should be <= 0 to distinguish from startup errors */
}

static int suphpd_start(apr_pool_t *p, server_rec *main_server,
                      apr_proc_t *procnew) {
  daemon_should_exit = 0; /* clear setting from previous generation */
  if ((daemon_pid = fork()) < 0) {
    ap_log_error(APLOG_MARK, APLOG_ERR, errno, main_server,
                  "mod_suphpd: Couldn't spawn suphpd daemon process");
    return DECLINED;
  }
  else if (daemon_pid == 0) {
    if (pcgi == NULL) {
        apr_pool_create(&pcgi, p);
    }
    exit(suphpd_server(main_server) > 0 ? DAEMON_STARTUP_ERROR : -1);
  }
  procnew->pid = daemon_pid;
  procnew->err = procnew->in = procnew->out = NULL;
  apr_pool_note_subprocess(p, procnew, APR_KILL_AFTER_TIMEOUT);
#if APR_HAS_OTHER_CHILD
  apr_proc_other_child_register(procnew, suphpd_maint, procnew, NULL, p);
#endif
  return OK;
}

int wtfres = -666;
int wtfsucc = APR_SUCCESS;
char *omg = OPT_APACHE_USER;
static int suphpd_pre_config(apr_pool_t *pconf, apr_pool_t *plog,
                           apr_pool_t *ptemp)
{
  sockname = ap_append_pid(pconf, DEFAULT_SOCKET, ".");
  if (APR_SUCCESS != (wtfres = apr_uid_get(&sockuid, &sockgid, OPT_APACHE_USER, ptemp))) {
    return DECLINED;
  }
  return OK;
}

static int suphpd_init(apr_pool_t *p, apr_pool_t *plog, apr_pool_t *ptemp,
                     server_rec *main_server) {
  apr_proc_t *procnew = NULL;
  int first_time = 0;
  const char *userdata_key = "suphpd_init";
  int ret = OK;
  void *data = NULL;

  root_server = main_server;
  root_pool = p;

  apr_pool_userdata_get(&data, userdata_key, main_server->process->pool);
  if (!data) {
    first_time = 1;
    procnew = apr_pcalloc(main_server->process->pool, sizeof(*procnew));
    procnew->pid = -1;
    procnew->err = procnew->in = procnew->out = NULL;
    apr_pool_userdata_set((const void *)procnew, userdata_key,
                  apr_pool_cleanup_null, main_server->process->pool);
  }
  else {
    procnew = data;
  }

  if (!first_time) {
    parent_pid = getpid();
    sockname = ap_server_root_relative(p, sockname);
    ret = suphpd_start(p, main_server, procnew);
    if (ret != OK) {
      return ret;
    }
  }
  return ret;
}

#if APR_HAS_OTHER_CHILD
static void suphpd_maint(int reason, void *data, apr_wait_t status)
{
    apr_proc_t *proc = data;
    int mpm_state;
    int stopping;

    switch (reason) {
        case APR_OC_REASON_DEATH:
            apr_proc_other_child_unregister(data);
            /* If apache is not terminating or restarting,
             * restart the cgid daemon
             */
            stopping = 1; /* if MPM doesn't support query,
                           * assume we shouldn't restart daemon
                           */
            if (ap_mpm_query(AP_MPMQ_MPM_STATE, &mpm_state) == APR_SUCCESS &&
                mpm_state != AP_MPMQ_STOPPING) {
                stopping = 0;
            }
            if (!stopping) {
                if (status == DAEMON_STARTUP_ERROR) {
                    ap_log_error(APLOG_MARK, APLOG_CRIT, 0, NULL,
                                 "cgid daemon failed to initialize");
                }
                else {
                    ap_log_error(APLOG_MARK, APLOG_ERR, 0, NULL,
                                 "cgid daemon process died, restarting");
                    suphpd_start(root_pool, root_server, proc);
                }
            }
            break;
        case APR_OC_REASON_RESTART:
            /* don't do anything; server is stopping or restarting */
            apr_proc_other_child_unregister(data);
            break;
        case APR_OC_REASON_LOST:
            /* Restart the child cgid daemon process */
            apr_proc_other_child_unregister(data);
            suphpd_start(root_pool, root_server, proc);
            break;
        case APR_OC_REASON_UNREGISTER:
            /* we get here when pcgi is cleaned up; pcgi gets cleaned
             * up when pconf gets cleaned up
             */
            kill(proc->pid, SIGHUP); /* send signal to daemon telling it to die */

            /* Remove the cgi socket, we must do it here in order to try and
             * guarantee the same permissions as when the socket was created.
             */
            if (unlink(sockname) < 0 && errno != ENOENT) {
                ap_log_error(APLOG_MARK, APLOG_ERR, errno, NULL,
                             "Couldn't unlink unix domain socket %s",
                             sockname);
            }
            break;
    }
}
#endif

/*********************
  Auxiliary functions
 *********************/

static apr_status_t suphp_log_script_err(request_rec *r,
                                         apr_file_t *script_err) {
  char argsbuffer[HUGE_STRING_LEN];
  char *newline;
  apr_status_t rv;

  while ((rv = apr_file_gets(argsbuffer, HUGE_STRING_LEN, script_err)) ==
         APR_SUCCESS) {
    newline = strchr(argsbuffer, '\n');
    if (newline) {
      *newline = '\0';
    }
    ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r, "%s", argsbuffer);
  }

  return rv;
}

char *suphp_brigade_read(apr_pool_t *p, apr_bucket_brigade *bb, int bytes) {
  char *target_buf;
  char *next_byte;
  char *last_byte;
  apr_bucket *b;

  if (bytes == 0) {
    return NULL;
  }

  target_buf = (char *)apr_palloc(p, bytes + 1);
  next_byte = target_buf;
  last_byte = target_buf + bytes;

  for (b = APR_BRIGADE_FIRST(bb); b != APR_BRIGADE_SENTINEL(bb);
       b = APR_BUCKET_NEXT(b)) {
    const char *buf;
    apr_size_t size;
    apr_size_t i;
    if (apr_bucket_read(b, &buf, &size, APR_BLOCK_READ) == APR_SUCCESS) {
      for (i = 0; i < size; i++) {
        *next_byte = *buf;
        next_byte++;
        buf++;
        if (next_byte == last_byte) {
          *next_byte = 0;
          return target_buf;
        }
      }
    }
  }
  next_byte = 0;
  return target_buf;
}

/**************************
  Configuration processing
 **************************/

#define SUPHP_CONFIG_MODE_SERVER 1
#define SUPHP_CONFIG_MODE_DIRECTORY 2

#define SUPHP_ENGINE_OFF 0
#define SUPHP_ENGINE_ON 1
#define SUPHP_ENGINE_UNDEFINED 2

#ifndef SUPHP_PATH_TO_SUPHP
#define SUPHP_PATH_TO_SUPHP "/usr/sbin/suphp"
#endif

typedef struct {
  int engine;  // Status of suPHP_Engine
  char *php_config;
  int cmode;  // Server of directory configuration?
  char *target_user;
  char *target_group;
  apr_table_t *handlers;
  char *php_path;
} suphp_conf;

static void *suphp_create_dir_config(apr_pool_t *p, char *dir) {
  suphp_conf *cfg = (suphp_conf *)apr_pcalloc(p, sizeof(suphp_conf));

  cfg->php_config = NULL;
  cfg->engine = SUPHP_ENGINE_UNDEFINED;
  cfg->php_path = NULL;
  cfg->cmode = SUPHP_CONFIG_MODE_DIRECTORY;
  cfg->target_user = NULL;
  cfg->target_group = NULL;

  /* Create table with 0 initial elements */
  /* This size may be increased for performance reasons */
  cfg->handlers = apr_table_make(p, 0);

  return (void *)cfg;
}

static void *suphp_merge_dir_config(apr_pool_t *p, void *base,
                                    void *overrides) {
  suphp_conf *parent = (suphp_conf *)base;
  suphp_conf *child = (suphp_conf *)overrides;
  suphp_conf *merged = (suphp_conf *)apr_pcalloc(p, sizeof(suphp_conf));

  merged->cmode = SUPHP_CONFIG_MODE_DIRECTORY;

  if (child->php_config)
    merged->php_config = apr_pstrdup(p, child->php_config);
  else if (parent->php_config)
    merged->php_config = apr_pstrdup(p, parent->php_config);
  else
    merged->php_config = NULL;

  if (child->engine != SUPHP_ENGINE_UNDEFINED)
    merged->engine = child->engine;
  else
    merged->engine = parent->engine;

  if (child->target_user)
    merged->target_user = apr_pstrdup(p, child->target_user);
  else if (parent->target_user)
    merged->target_user = apr_pstrdup(p, parent->target_user);
  else
    merged->target_user = NULL;

  if (child->target_group)
    merged->target_group = apr_pstrdup(p, child->target_group);
  else if (parent->target_group)
    merged->target_group = apr_pstrdup(p, parent->target_group);
  else
    merged->target_group = NULL;

  merged->handlers = apr_table_overlay(p, child->handlers, parent->handlers);

  return (void *)merged;
}

static void *suphp_create_server_config(apr_pool_t *p, server_rec *s) {
  suphp_conf *cfg = (suphp_conf *)apr_pcalloc(p, sizeof(suphp_conf));

  cfg->engine = SUPHP_ENGINE_UNDEFINED;
  cfg->php_path = NULL;
  cfg->cmode = SUPHP_CONFIG_MODE_SERVER;

  /* Create table with 0 initial elements */
  /* This size may be increased for performance reasons */
  cfg->handlers = apr_table_make(p, 0);

  return (void *)cfg;
}

static void *suphp_merge_server_config(apr_pool_t *p, void *base,
                                       void *overrides) {
  suphp_conf *parent = (suphp_conf *)base;
  suphp_conf *child = (suphp_conf *)overrides;
  suphp_conf *merged = (suphp_conf *)apr_pcalloc(p, sizeof(suphp_conf));

  if (child->engine != SUPHP_ENGINE_UNDEFINED)
    merged->engine = child->engine;
  else
    merged->engine = parent->engine;

  if (child->php_path != NULL)
    merged->php_path = apr_pstrdup(p, child->php_path);
  else
    merged->php_path = apr_pstrdup(p, parent->php_path);

  if (child->target_user)
    merged->target_user = apr_pstrdup(p, child->target_user);
  else if (parent->target_user)
    merged->target_user = apr_pstrdup(p, parent->target_user);
  else
    merged->target_user = NULL;

  if (child->target_group)
    merged->target_group = apr_pstrdup(p, child->target_group);
  else if (parent->target_group)
    merged->target_group = apr_pstrdup(p, parent->target_group);
  else
    merged->target_group = NULL;

  merged->handlers = apr_table_overlay(p, child->handlers, parent->handlers);

  return (void *)merged;
}

/******************
  Command handlers
 ******************/

static const char *suphp_handle_cmd_engine(cmd_parms *cmd, void *mconfig,
                                           int flag) {
  server_rec *s = cmd->server;
  suphp_conf *cfg;

  if (mconfig)
    cfg = (suphp_conf *)mconfig;
  else
    cfg = (suphp_conf *)ap_get_module_config(s->module_config, &suphpd_module);

  if (flag)
    cfg->engine = SUPHP_ENGINE_ON;
  else
    cfg->engine = SUPHP_ENGINE_OFF;

  return NULL;
}

static const char *suphp_handle_cmd_config(cmd_parms *cmd, void *mconfig,
                                           const char *arg) {
  server_rec *s = cmd->server;
  suphp_conf *cfg;

  if (mconfig)
    cfg = (suphp_conf *)mconfig;
  else
    cfg = (suphp_conf *)ap_get_module_config(s->module_config, &suphpd_module);

  cfg->php_config = apr_pstrdup(cmd->pool, arg);

  return NULL;
}

static const char *suphp_handle_cmd_user_group(cmd_parms *cmd, void *mconfig,
                                               const char *arg1,
                                               const char *arg2) {
  suphp_conf *cfg = (suphp_conf *)mconfig;

  cfg->target_user = apr_pstrdup(cmd->pool, arg1);
  cfg->target_group = apr_pstrdup(cmd->pool, arg2);

  return NULL;
}

static const char *suphp_handle_cmd_add_handler(cmd_parms *cmd, void *mconfig,
                                                const char *arg) {
  suphp_conf *cfg;
  if (mconfig)
    cfg = (suphp_conf *)mconfig;
  else
    cfg = (suphp_conf *)ap_get_module_config(cmd->server->module_config,
                                             &suphpd_module);

  // Mark active handler with '1'
  apr_table_set(cfg->handlers, arg, "1");

  return NULL;
}

static const char *suphp_handle_cmd_remove_handler(cmd_parms *cmd,
                                                   void *mconfig,
                                                   const char *arg) {
  suphp_conf *cfg;
  if (mconfig)
    cfg = (suphp_conf *)mconfig;
  else
    cfg = (suphp_conf *)ap_get_module_config(cmd->server->module_config,
                                             &suphpd_module);

  // Mark deactivated handler with '0'
  apr_table_set(cfg->handlers, arg, "0");

  return NULL;
}

static const char *suphp_handle_cmd_phppath(cmd_parms *cmd, void *mconfig,
                                            const char *arg) {
  server_rec *s = cmd->server;
  suphp_conf *cfg;

  cfg = (suphp_conf *)ap_get_module_config(s->module_config, &suphpd_module);

  cfg->php_path = apr_pstrdup(cmd->pool, arg);

  return NULL;
}

static const char *set_script_socket(cmd_parms *cmd, void *dummy, const char *arg) {
  const char *err = ap_check_cmd_context(cmd, GLOBAL_ONLY);
  if (err != NULL) {
    return err;
  }

  /* Make sure the pid is appended to the sockname */
  sockname = ap_append_pid(cmd->pool, arg, ".");
  sockname = ap_server_root_relative(cmd->pool, sockname);

  if (!sockname) {
    return apr_pstrcat(cmd->pool, "Invalid suPHP_ScriptSock path",
                        arg, NULL);
  }

  return NULL;
}

static const command_rec suphp_cmds[] = {
    AP_INIT_FLAG("suPHP_Engine", suphp_handle_cmd_engine, NULL,
                 RSRC_CONF | ACCESS_CONF,
                 "Whether suPHP is on or off, default is off"),
    AP_INIT_TAKE1("suPHP_ConfigPath", suphp_handle_cmd_config, NULL, OR_OPTIONS,
                  "Wheres the php.ini resides, default is the PHP default"),
    AP_INIT_TAKE2("suPHP_UserGroup", suphp_handle_cmd_user_group, NULL,
                  RSRC_CONF | ACCESS_CONF,
                  "User and group scripts shall be run as"),
    AP_INIT_ITERATE("suPHP_AddHandler", suphp_handle_cmd_add_handler, NULL,
                    RSRC_CONF | ACCESS_CONF,
                    "Tells mod_suphp to handle these MIME-types"),
    AP_INIT_ITERATE("suPHP_RemoveHandler", suphp_handle_cmd_remove_handler,
                    NULL, RSRC_CONF | ACCESS_CONF,
                    "Tells mod_suphp not to handle these MIME-types"),
    AP_INIT_TAKE1("suPHP_PHPPath", suphp_handle_cmd_phppath, NULL, RSRC_CONF,
                  "Path to the PHP binary used to render source view"),
    AP_INIT_TAKE1("suPHP_ScriptSock", set_script_socket, NULL, RSRC_CONF,
                  "the name of the socket to use for communication with "
                  "the cgi daemon."),
    {NULL}};

/*****************************************
  Code for reading script's stdout/stderr
  based on mod_cgi's code
 *****************************************/

#if APR_FILES_AS_SOCKETS

static const apr_bucket_type_t bucket_type_suphp;

struct suphp_bucket_data {
  apr_pollset_t *pollset;
  request_rec *r;
};

static apr_bucket *suphp_bucket_create(request_rec *r, apr_file_t *out,
                                       apr_file_t *err,
                                       apr_bucket_alloc_t *list) {
  apr_bucket *b = apr_bucket_alloc(sizeof(*b), list);
  apr_pollfd_t fd;
  struct suphp_bucket_data *data = apr_palloc(r->pool, sizeof(*data));

  APR_BUCKET_INIT(b);
  b->free = apr_bucket_free;
  b->list = list;
  b->type = &bucket_type_suphp;
  b->length = (apr_size_t)(-1);
  b->start = (-1);

  /* Create the pollset */
  apr_pollset_create(&data->pollset, 2, r->pool, 0);

  fd.desc_type = APR_POLL_FILE;
  fd.reqevents = APR_POLLIN;
  fd.p = r->pool;
  fd.desc.f = out; /* script's stdout */
  fd.client_data = (void *)1;
  apr_pollset_add(data->pollset, &fd);

  fd.desc.f = err; /* script's stderr */
  fd.client_data = (void *)2;
  apr_pollset_add(data->pollset, &fd);

  data->r = r;
  b->data = data;
  return b;
}

static apr_bucket *suphp_bucket_dup(struct suphp_bucket_data *data,
                                    apr_bucket_alloc_t *list) {
  apr_bucket *b = apr_bucket_alloc(sizeof(*b), list);
  APR_BUCKET_INIT(b);
  b->free = apr_bucket_free;
  b->list = list;
  b->type = &bucket_type_suphp;
  b->length = (apr_size_t)(-1);
  b->start = (-1);
  b->data = data;
  return b;
}

/* This utility method is needed, because APR's implementation for the
   pipe bucket cannot handle or special bucket type                    */
static apr_status_t suphp_read_fd(apr_bucket *b, apr_file_t *fd,
                                  const char **str, apr_size_t *len) {
  char *buf;
  apr_status_t rv;

  *str = NULL;
  *len = APR_BUCKET_BUFF_SIZE;
  buf = apr_bucket_alloc(*len, b->list);

  rv = apr_file_read(fd, buf, len);

  if (*len > 0) {
    /* Got data */
    struct suphp_bucket_data *data = b->data;
    apr_bucket_heap *h;

    /* Change the current bucket to refer to what we read
       and append the pipe bucket after it                */
    b = apr_bucket_heap_make(b, buf, *len, apr_bucket_free);
    /* Here, b->data is the new heap bucket data */
    h = b->data;
    h->alloc_len = APR_BUCKET_BUFF_SIZE; /* note the real buffer size */
    *str = buf;
    APR_BUCKET_INSERT_AFTER(b, suphp_bucket_dup(data, b->list));
  } else {
    /* Got no data */
    apr_bucket_free(buf);
    b = apr_bucket_immortal_make(b, "", 0);
    /* Here, b->data is the reference to the empty string */
    *str = b->data;
  }
  return rv;
}

/* Poll on stdout and stderr to make sure the process does not block
   because of a full system (stderr) buffer                          */
static apr_status_t suphp_bucket_read(apr_bucket *b, const char **str,
                                      apr_size_t *len, apr_read_type_e block) {
  struct suphp_bucket_data *data = b->data;
  apr_interval_time_t timeout;
  apr_status_t rv;
  int gotdata = 0;

  /* Some modules check the length rather than the returned status */
  *len = 0;

  timeout = (block == APR_NONBLOCK_READ) ? 0 : data->r->server->timeout;

  do {
    const apr_pollfd_t *results;
    apr_int32_t num;

    rv = apr_pollset_poll(data->pollset, timeout, &num, &results);
    if (APR_STATUS_IS_TIMEUP(rv)) {
      return (timeout == 0) ? APR_EAGAIN : rv;
    } else if (APR_STATUS_IS_EINTR(rv)) {
      continue;
    } else if (rv != APR_SUCCESS) {
      ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, data->r,
                    "Poll failed waiting for suPHP child process");
      return rv;
    }

    while (num > 0) {
      if (results[0].client_data == (void *)1) {
        /* handle stdout */
        rv = suphp_read_fd(b, results[0].desc.f, str, len);
        if (APR_STATUS_IS_EOF(rv)) {
          rv = APR_SUCCESS;
        }
        gotdata = 1;
      } else {
        /* handle stderr */
        apr_status_t rv2 = suphp_log_script_err(data->r, results[0].desc.f);
        if (APR_STATUS_IS_EOF(rv2)) {
          apr_pollset_remove(data->pollset, &results[0]);
        }
      }
      num--;
      results++;
    }
  } while (!gotdata);

  return rv;
}

static const apr_bucket_type_t bucket_type_suphp = {"SUPHP",
                                                    5,
                                                    APR_BUCKET_DATA,
                                                    apr_bucket_destroy_noop,
                                                    suphp_bucket_read,
                                                    apr_bucket_setaside_notimpl,
                                                    apr_bucket_split_notimpl,
                                                    apr_bucket_copy_notimpl};

#endif

static void suphp_discard_output(apr_bucket_brigade *bb) {
  apr_bucket *b;
  const char *buf;
  apr_size_t len;
  apr_status_t rv;
  for (b = APR_BRIGADE_FIRST(bb); b != APR_BRIGADE_SENTINEL(bb);
       b = APR_BUCKET_NEXT(b)) {
    if (APR_BUCKET_IS_EOS(b)) {
      break;
    }
    rv = apr_bucket_read(b, &buf, &len, APR_BLOCK_READ);
    if (rv != APR_SUCCESS) {
      break;
    }
  }
}

/******************
  Hooks / handlers
 ******************/

static int suphp_script_handler(request_rec *r);
static int suphp_source_handler(request_rec *r);

static int suphp_handler(request_rec *r) {
  suphp_conf *sconf, *dconf;

  sconf = ap_get_module_config(r->server->module_config, &suphpd_module);
  dconf = ap_get_module_config(r->per_dir_config, &suphpd_module);

  /* only handle request if mod_suphp is active for this handler */
  /* check only first byte of value (second has to be \0) */
  if (apr_table_get(dconf->handlers, r->handler) != NULL) {
    if (*(apr_table_get(dconf->handlers, r->handler)) != '0') {
      return suphp_script_handler(r);
    }
  } else {
    if ((apr_table_get(sconf->handlers, r->handler) != NULL) &&
        (*(apr_table_get(sconf->handlers, r->handler)) != '0')) {
      return suphp_script_handler(r);
    }
  }

  if (!strcmp(r->handler, "x-httpd-php-source") ||
      !strcmp(r->handler, "application/x-httpd-php-source")) {
    return suphp_source_handler(r);
  }

  return DECLINED;
}

static int suphp_source_handler(request_rec *r) {
  suphp_conf *conf;
  apr_status_t rv;
  apr_pool_t *p = r->main ? r->main->pool : r->pool;
  apr_file_t *file;
  apr_proc_t *proc;
  apr_procattr_t *procattr;
  char **argv;
  char **env;
  apr_bucket_brigade *bb;
  apr_bucket *b;
  char *phpexec;
  apr_table_t *empty_table = apr_table_make(p, 0);

  if (strcmp(r->method, "GET")) {
    return DECLINED;
  }

  conf = ap_get_module_config(r->server->module_config, &suphpd_module);
  phpexec = apr_pstrdup(p, conf->php_path);
  if (phpexec == NULL) {
    return DECLINED;
  }

  // Try to open file for reading to see whether is is accessible
  rv = apr_file_open(&file, apr_pstrdup(p, r->filename), APR_READ,
                     APR_OS_DEFAULT, p);
  if (rv == APR_SUCCESS) {
    apr_file_close(file);
    file = NULL;
  } else if (rv == EACCES) {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, r, "access to %s denied",
                  r->filename);
    return HTTP_FORBIDDEN;
  } else if (rv == ENOENT) {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r, "File does not exist: %s",
                  r->filename);
    return HTTP_NOT_FOUND;
  } else {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, r, "Could not open file: %s",
                  r->filename);
    return HTTP_INTERNAL_SERVER_ERROR;
  }

  /* set attributes for new process */

  if (((rv = apr_procattr_create(&procattr, p)) != APR_SUCCESS) ||
      ((rv = apr_procattr_io_set(procattr, APR_CHILD_BLOCK, APR_CHILD_BLOCK,
                                 APR_CHILD_BLOCK)) != APR_SUCCESS) ||
      ((rv = apr_procattr_dir_set(
            procattr, ap_make_dirstr_parent(r->pool, r->filename))) !=
       APR_SUCCESS) ||
      ((apr_procattr_cmdtype_set(procattr, APR_PROGRAM)) != APR_SUCCESS) ||
      ((apr_procattr_error_check_set(procattr, 1)) != APR_SUCCESS) ||
      ((apr_procattr_detach_set(procattr, 0)) != APR_SUCCESS)) {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, r,
                  "couldn't set child process attributes: %s", r->filename);
    return HTTP_INTERNAL_SERVER_ERROR;
  }

  /* create new process */

  argv = apr_palloc(p, 4 * sizeof(char *));
  argv[0] = phpexec;
  argv[1] = "-s";
  argv[2] = apr_pstrdup(p, r->filename);
  argv[3] = NULL;

  env = ap_create_environment(p, empty_table);

  proc = apr_pcalloc(p, sizeof(*proc));
  rv = apr_proc_create(proc, phpexec, (const char *const *)argv,
                       (const char *const *)env, procattr, p);
  if (rv != APR_SUCCESS) {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, r,
                  "couldn't create child process: %s for %s", phpexec,
                  r->filename);
    return HTTP_INTERNAL_SERVER_ERROR;
  }
  apr_pool_note_subprocess(p, proc, APR_KILL_AFTER_TIMEOUT);

  if (!proc->out) return APR_EBADF;
  apr_file_pipe_timeout_set(proc->out, r->server->timeout);

  if (!proc->in) return APR_EBADF;
  apr_file_pipe_timeout_set(proc->in, r->server->timeout);

  if (!proc->err) return APR_EBADF;
  apr_file_pipe_timeout_set(proc->err, r->server->timeout);

  /* discard input */

  bb = apr_brigade_create(r->pool, r->connection->bucket_alloc);

  apr_file_flush(proc->in);
  apr_file_close(proc->in);

  rv = ap_get_brigade(r->input_filters, bb, AP_MODE_READBYTES, APR_BLOCK_READ,
                      HUGE_STRING_LEN);
  if (rv != APR_SUCCESS) {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, r,
                  "couldn't get input from filters: %s", r->filename);
    return HTTP_INTERNAL_SERVER_ERROR;
  }
  suphp_discard_output(bb);
  apr_brigade_cleanup(bb);

/* get output from script */

#if APR_FILES_AS_SOCKETS
  apr_file_pipe_timeout_set(proc->out, 0);
  apr_file_pipe_timeout_set(proc->err, 0);
  b = suphp_bucket_create(r, proc->out, proc->err, r->connection->bucket_alloc);
#else
  b = apr_bucket_pipe_create(proc->out, r->connection->bucket_alloc);
#endif
  APR_BRIGADE_INSERT_TAIL(bb, b);

  b = apr_bucket_eos_create(r->connection->bucket_alloc);
  APR_BRIGADE_INSERT_TAIL(bb, b);

  /* send output to browser (through filters) */

  r->content_type = "text/html";
  rv = ap_pass_brigade(r->output_filters, bb);

  /* write errors to logfile */

  if (rv == APR_SUCCESS && !r->connection->aborted) {
    suphp_log_script_err(r, proc->err);
    apr_file_close(proc->err);
  }

  return OK;
}

static int suphp_script_handler(request_rec *r) {
  apr_pool_t *p;
  suphp_conf *sconf;
  suphp_conf *dconf;

  apr_finfo_t finfo;

  int sd;
  apr_file_t *sd_file;

  char **env;
  apr_status_t rv;
#if MAX_STRING_LEN < 1024
  char strbuf[1024];
#else
  char strbuf[MAX_STRING_LEN];
#endif
  char *tmpbuf;
  int nph = 0;
  int eos_reached = 0;
  int child_stopped_reading = 0;
  char *auth_user = NULL;
  char *auth_pass = NULL;

  char *ud_user = NULL;
  char *ud_group = NULL;
  int ud_success = 0;
  ap_unix_identity_t *userdir_id = NULL;

  apr_bucket_brigade *bb;
  apr_bucket *b;

  /* load configuration */

  p = r->main ? r->main->pool : r->pool;
  sconf = ap_get_module_config(r->server->module_config, &suphpd_module);
  dconf = ap_get_module_config(r->per_dir_config, &suphpd_module);

  /* check if suPHP is enabled for this request */

  if (((sconf->engine != SUPHP_ENGINE_ON) &&
       (dconf->engine != SUPHP_ENGINE_ON)) ||
      ((sconf->engine == SUPHP_ENGINE_ON) &&
       (dconf->engine == SUPHP_ENGINE_OFF)))
    return DECLINED;

  /* check if file is existing and acessible */

  rv = apr_stat(&finfo, apr_pstrdup(p, r->filename), APR_FINFO_NORM, p);

  if (rv == APR_SUCCESS)
    ; /* do nothing */
  else if (rv == EACCES) {
    return HTTP_FORBIDDEN;
    ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, r, "access to %s denied",
                  r->filename);
  } else if (rv == ENOENT) {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r, "File does not exist: %s",
                  r->filename);
    return HTTP_NOT_FOUND;
  } else {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, r, "could not get fileinfo: %s",
                  r->filename);
    return HTTP_NOT_FOUND;
  }

  if (!(r->finfo.protection & APR_UREAD)) {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r, "Insufficient permissions: %s",
                  r->filename);
    return HTTP_FORBIDDEN;
  }

  /* Check for userdir request */
  userdir_id = ap_run_get_suexec_identity(r);
  if (userdir_id != NULL && userdir_id->userdir) {
    ud_user = apr_psprintf(r->pool, "#%ld", (long)userdir_id->uid);
    ud_group = apr_psprintf(r->pool, "#%ld", (long)userdir_id->gid);
    ud_success = 1;
  }

  /* prepare environment for new process */

  ap_add_common_vars(r);
  ap_add_cgi_vars(r);

  apr_table_unset(r->subprocess_env, "SUPHP_PHP_CONFIG");
  apr_table_unset(r->subprocess_env, "SUPHP_AUTH_USER");
  apr_table_unset(r->subprocess_env, "SUPHP_AUTH_PW");
  apr_table_unset(r->subprocess_env, "SUPHP_USER");
  apr_table_unset(r->subprocess_env, "SUPHP_GROUP");
  apr_table_unset(r->subprocess_env, "SUPHP_USERDIR_USER");
  apr_table_unset(r->subprocess_env, "SUPHP_USERDIR_GROUP");

  if (dconf->php_config) {
    apr_table_setn(r->subprocess_env, "SUPHP_PHP_CONFIG",
                   apr_pstrdup(p, dconf->php_config));
  }

  apr_table_setn(r->subprocess_env, "SUPHP_HANDLER", r->handler);

  if (r->headers_in) {
    const char *auth = NULL;
    auth = apr_table_get(r->headers_in, "Authorization");
    if (auth && auth[0] != 0 && strncmp(auth, "Basic ", 6) == 0) {
      char *user;
      char *pass;
      user = ap_pbase64decode(p, auth + 6);
      if (user) {
        pass = strchr(user, ':');
        if (pass) {
          *pass++ = '\0';
          auth_user = apr_pstrdup(r->pool, user);
          auth_pass = apr_pstrdup(r->pool, pass);
        }
      }
    }
  }

  if (auth_user && auth_pass) {
    apr_table_setn(r->subprocess_env, "SUPHP_AUTH_USER", auth_user);
    apr_table_setn(r->subprocess_env, "SUPHP_AUTH_PW", auth_pass);
  }

  if (dconf->target_user) {
    apr_table_setn(r->subprocess_env, "SUPHP_USER",
                   apr_pstrdup(r->pool, dconf->target_user));
  } else if (sconf->target_user) {
    apr_table_setn(r->subprocess_env, "SUPHP_USER",
                   apr_pstrdup(r->pool, sconf->target_user));
  }

  if (dconf->target_group) {
    apr_table_setn(r->subprocess_env, "SUPHP_GROUP",
                   apr_pstrdup(r->pool, dconf->target_group));
  } else if (sconf->target_group) {
    apr_table_setn(r->subprocess_env, "SUPHP_GROUP",
                   apr_pstrdup(r->pool, sconf->target_group));
  }

  if (ud_success) {
    apr_table_setn(r->subprocess_env, "SUPHP_USERDIR_USER",
                   apr_pstrdup(r->pool, ud_user));
    apr_table_setn(r->subprocess_env, "SUPHP_USERDIR_GROUP",
                   apr_pstrdup(r->pool, ud_group));
  }

  env = ap_create_environment(p, r->subprocess_env);

  /* create new process */

  if (OK != (rv = connect_to_daemon(&sd, r))) return rv;
  rv = send_req(sd, r, env, PHP_REQ);
  if (rv != APR_SUCCESS) {
    ap_log_rerror(APLOG_MARK, APLOG_ERR, rv, r,
                  "couldn't create child process: %s for %s",
                  SUPHP_PATH_TO_SUPHP, r->filename);
    return HTTP_INTERNAL_SERVER_ERROR;
  }

  /* We are putting the socket discriptor into an apr_file_t so that we can
    * use a pipe bucket to send the data to the client.  APR will create
    * a cleanup for the apr_file_t which will close the socket, so we'll
    * get rid of the cleanup we registered when we created the socket.
    */
  apr_os_pipe_put_ex(&sd_file, &sd, 1, r->pool);
  apr_file_pipe_timeout_set(sd_file, r->server->timeout);
  apr_pool_cleanup_kill(r->pool, (void *)((long)sd), close_unix_socket);

  /* send request body to script */

  bb = apr_brigade_create(r->pool, r->connection->bucket_alloc);
  do {
    apr_bucket *bucket;
    rv = ap_get_brigade(r->input_filters, bb, AP_MODE_READBYTES, APR_BLOCK_READ,
                        HUGE_STRING_LEN);

    if (rv != APR_SUCCESS) {
      return rv;
    }

    for (bucket = APR_BRIGADE_FIRST(bb); bucket != APR_BRIGADE_SENTINEL(bb);
         bucket = APR_BUCKET_NEXT(bucket)) {
      const char *data;
      apr_size_t len;

      if (APR_BUCKET_IS_EOS(bucket)) {
        eos_reached = 1;
        break;
      }

      if (APR_BUCKET_IS_FLUSH(bucket) || child_stopped_reading) {
        continue;
      }

      apr_bucket_read(bucket, &data, &len, APR_BLOCK_READ);

      rv = apr_file_write_full(sd_file, data, len, NULL);
      if (rv != APR_SUCCESS) {
        child_stopped_reading = 1;
      }
    }
    apr_brigade_cleanup(bb);
  } while (!eos_reached);

  apr_file_flush(sd_file);
  shutdown(sd, SHUT_WR);

/* get output from script and check if non-parsed headers are used */

  b = apr_bucket_pipe_create(sd_file, r->connection->bucket_alloc);

  APR_BRIGADE_INSERT_TAIL(bb, b);

  b = apr_bucket_eos_create(r->connection->bucket_alloc);
  APR_BRIGADE_INSERT_TAIL(bb, b);

  tmpbuf = suphp_brigade_read(p, bb, 8);
  if (strlen(tmpbuf) == 8 &&
      !(strncmp(tmpbuf, "HTTP/1.0", 8) && strncmp(tmpbuf, "HTTP/1.1", 8))) {
    nph = 1;
  }

  if (!nph) {
    /* normal cgi headers, so we have to create the real headers ourselves */

    int ret;
    const char *location;

    ret = ap_scan_script_header_err_brigade(r, bb, strbuf);
    if (ret == HTTP_NOT_MODIFIED) {
      return ret;
    } else if (ret != APR_SUCCESS) {
      suphp_discard_output(bb);
      apr_brigade_destroy(bb);

      /* ap_scan_script_header_err_brigade does logging itself,
         so simply return                                       */

      return HTTP_INTERNAL_SERVER_ERROR;
    }

    location = apr_table_get(r->headers_out, "Location");
    if (location && location[0] == '/' && r->status == 200) {
      /* empty brigade (script output) and modify headers */

      suphp_discard_output(bb);
      apr_brigade_destroy(bb);
      r->method = apr_pstrdup(r->pool, "GET");
      r->method_number = M_GET;
      apr_table_unset(r->headers_in, "Content-Length");

      ap_internal_redirect_handler(location, r);
      return OK;
    } else if (location && r->status == 200) {
      /* empty brigade (script output) */
      suphp_discard_output(bb);
      apr_brigade_destroy(bb);
      return HTTP_MOVED_TEMPORARILY;
    }

    /* send output to browser (through filters) */

    rv = ap_pass_brigade(r->output_filters, bb);
  }

  if (nph) {
    /* use non-parsed headers (direct output) */

    struct ap_filter_t *cur;

    /* get rid of output filters */

    cur = r->proto_output_filters;
    while (cur && cur->frec->ftype < AP_FTYPE_CONNECTION) {
      cur = cur->next;
    }
    r->output_filters = r->proto_output_filters = cur;

    /* send output to browser (directly) */

    rv = ap_pass_brigade(r->output_filters, bb);
  }

  return OK;
}

static void suphp_register_hooks(apr_pool_t *p) {
  ap_hook_pre_config(suphpd_pre_config, NULL, NULL, APR_HOOK_MIDDLE);
  ap_hook_post_config(suphpd_init, NULL, NULL, APR_HOOK_MIDDLE);
  ap_hook_handler(suphp_handler, NULL, NULL, APR_HOOK_MIDDLE);
}

/********************
  Module declaration
 ********************/
/* clang-format off */
module AP_MODULE_DECLARE_DATA suphpd_module = {
  STANDARD20_MODULE_STUFF,
  suphp_create_dir_config,
  suphp_merge_dir_config,
  suphp_create_server_config,
  suphp_merge_server_config,
  suphp_cmds,
  suphp_register_hooks
};
