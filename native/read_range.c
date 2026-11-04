/*
 * The checker's one native read (`readRangeIO`, ConLeche/Frontend/ReadRange.lean):
 * a stateless positional read, `pread(2)` of `len` bytes at `off` of the
 * regular file `path`.  The file is opened, read and closed in the call.
 *
 * What it returns is the model's slice of the file's bytes
 * (`ByteArray.extract off (min (off + len) size)` in
 * `ConLeche/Frontend/CheckerIO.lean`): the bytes from `off` up to
 * `off + len` or the end of the file, whichever comes first, so a read at
 * or past the end is empty.  The buffer is sized by that slice, never by
 * `len` alone.  Every failure of a system call, `close` included, is an
 * `IO.Error` (the runtime's decoding of `errno`); a read whose `close`
 * fails returns that error, not its bytes, and the descriptor is not
 * closed a second time (on Linux it is released whatever `close` returns).
 *
 * PLATFORM ASSUMPTIONS, checked at compile time where C can check them:
 *   - POSIX `open` with `O_CLOEXEC`, `fstat`, `pread` (Linux, macOS);
 *   - a 64-bit `off_t` (`_FILE_OFFSET_BITS 64` asks for it on 32-bit
 *     glibc; the static assertion below refuses a build without it), so
 *     every offset the Lean side passes (below 2^63, `readRangeOf` in
 *     CheckerIO.lean) is an `off_t`;
 *   - a 64-bit `size_t`, so a slice length (at most the file's size,
 *     below 2^63) is a `size_t` and a Lean `ByteArray` size;
 *   - each `pread` request is at most `SSIZE_MAX` bytes (its result is a
 *     `ssize_t`); a longer slice is read by the loop, request by request.
 * The allocation of the slice is the runtime's (`lean_alloc_sarray`),
 * which ends the process on out-of-memory as every Lean allocation does.
 */
#define _FILE_OFFSET_BITS 64
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

_Static_assert(sizeof(off_t) == 8, "read_range.c needs a 64-bit off_t");
_Static_assert(sizeof(size_t) == 8, "read_range.c needs a 64-bit size_t");

static lean_obj_res read_range_error(int err, b_lean_obj_arg path) {
  return lean_io_result_mk_error(lean_decode_io_error(err, path));
}

/* close `fd` after a failure `err`: the first failure is the one reported */
static lean_obj_res read_range_fail(int fd, int err, b_lean_obj_arg path) {
  close(fd);
  return read_range_error(err, path);
}

LEAN_EXPORT lean_obj_res conleche_read_range(b_lean_obj_arg path, uint64_t off, uint64_t len,
                                             lean_obj_arg w) {
  int fd = open(lean_string_cstr(path), O_RDONLY | O_CLOEXEC);
  if (fd < 0) return read_range_error(errno, path);
  struct stat st;
  if (fstat(fd, &st) != 0) return read_range_fail(fd, errno, path);
  if (!S_ISREG(st.st_mode))
    return read_range_fail(fd, S_ISDIR(st.st_mode) ? EISDIR : EINVAL, path);
  if (st.st_size < 0) return read_range_fail(fd, EINVAL, path);
  uint64_t size = (uint64_t)st.st_size;
  uint64_t n = off >= size ? 0 : (len < size - off ? len : size - off);
  lean_object *arr = lean_alloc_sarray(1, 0, (size_t)n);
  uint8_t *buf = lean_sarray_cptr(arr);
  uint64_t got = 0;
  while (got < n) {
    uint64_t want = n - got;
    if (want > (uint64_t)SSIZE_MAX) want = (uint64_t)SSIZE_MAX;
    ssize_t r = pread(fd, buf + got, (size_t)want, (off_t)(off + got));
    if (r < 0) {
      if (errno == EINTR) continue;
      int err = errno;
      lean_dec_ref(arr);
      return read_range_fail(fd, err, path);
    }
    if (r == 0) break; /* the file ended early: it is shorter than it was */
    got += (uint64_t)r;
  }
  if (close(fd) != 0) {
    int err = errno;
    lean_dec_ref(arr);
    return read_range_error(err, path);
  }
  lean_sarray_object *sa = lean_to_sarray(arr);
  sa->m_size = (size_t)got;
  return lean_io_result_mk_ok(arr);
}
