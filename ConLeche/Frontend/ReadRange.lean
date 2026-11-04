module

@[expose] public section

/-!
# The one native read: a stateless positional read

`readRangeIO path off len` is `pread(2)` of `len` bytes at offset `off`
of the regular file `path` (`native/read_range.c`: the file opened, read
and closed in the call): the bytes from `off` up to `off + len` or the
end of the file, whichever comes first, so a read at or past the end is
empty; a path that names no regular file, and every failure of the
system calls (`close` included: a read whose `close` fails returns the
error, not its bytes), is an `IO.Error`.  Its platform assumptions —
POSIX `pread` and `O_CLOEXEC`, a 64-bit `off_t` and `size_t` (refused at
compile time otherwise), requests of at most `SSIZE_MAX` bytes each —
are stated in the C file.  The Lean side passes it only offsets below
`2^63` and lengths below `2^63` (`readRangeOf`,
`ConLeche/Frontend/CheckerIO.lean`), and the slice it returns is no
longer than the file, so its size is a Lean `ByteArray` size.  Lean's file handles have no positional
read, so this is a C function, the one the checker carries; the binary's
instance of the IO class reads every file through it
(`CheckerIO.readRange`, `ConLeche/Frontend/CheckerIO.lean`), and the
model's read is the slice `ByteArray.extract off (off + len)` of the
snapshot's bytes.

It is its own library (`ConLecheNative` in `lakefile.lean`), compiled to
native code, so that the interpreter (the test library's `#eval`s) can
call it too.
-/

namespace ConLeche

/-- **A positional read** of a regular file: `len` bytes at `off`, fewer
at the end of the file (`native/read_range.c`). -/
@[extern "conleche_read_range"]
opaque readRangeIO (path : @& String) (off len : UInt64) : IO ByteArray

end ConLeche
