\ bench.fs -- portable Forth benchmark suite
\ Compatible with BadgerForth, gForth, pForth
\ Usage: include bench.fs   or   gforth bench.fs

variable bench-xt

: bench-loop ( xt n -- )
  swap bench-xt !
  0 do bench-xt @ execute loop ;

: bench-header ( -- )
  cr ." ==============================" cr
     ." Forth Benchmark Suite"          cr
     ." ==============================" cr cr ;

: bench-done ( -- ) ." done" cr ;

\ ----------------------------------------------------------------
\ 1. Empty loop -- raw loop + execute overhead
\ ----------------------------------------------------------------
: bench-noop ( -- ) ;

: do-bench-empty-loop ( -- )
  ." --- 1. Empty loop 10M ---" cr
  ['] bench-noop 10000000 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ 2. Fibonacci (recursive)
\ ----------------------------------------------------------------
: fib ( n -- fib[n] )
  dup 2 < if exit then
  dup 1- recurse
  swap 2 - recurse
  + ;

: fib-once ( -- ) 25 fib drop ;

: do-bench-fib ( -- )
  ." --- 2. fib(25) verify=75025: " 25 fib . cr
  ['] fib-once 1000 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ 3. Counted loop with arithmetic
\ ----------------------------------------------------------------
: sum-to-n ( n -- sum )
  0 swap 1+ 1 do i + loop ;

: sum-once ( -- ) 1000 sum-to-n drop ;

: do-bench-sum ( -- )
  ." --- 3. sum 1..1000 verify=500500: " 1000 sum-to-n . cr
  ['] sum-once 100000 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ 4. Sieve of Eratosthenes
\ ----------------------------------------------------------------
8192 constant sieve-size
create sieve-buf sieve-size allot

: sieve ( -- prime-count )
  sieve-buf sieve-size 1 fill
  0 sieve-buf c!
  0 sieve-buf 1+ c!
  2
  begin
    dup dup * sieve-size <
  while
    dup sieve-buf + c@ if
      dup dup *
      begin dup sieve-size < while
        0 over sieve-buf + c!
        over +
      repeat
      drop
    then
    1+
  repeat
  drop
  0 sieve-size 0 do sieve-buf i + c@ + loop ;

: sieve-once ( -- ) sieve drop ;

: do-bench-sieve ( -- )
  ." --- 4. Sieve(8192) verify=1028: " sieve . cr
  ['] sieve-once 1000 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ 5. Ackermann(3,5)
\ ----------------------------------------------------------------
: ack ( m n -- result )
  over 0= if nip 1+ exit then
  dup  0= if drop 1- 1 recurse exit then
  over 1- >r
  1- recurse
  r> swap recurse ;

: ack-once ( -- ) 3 5 ack drop ;

: do-bench-ack ( -- )
  ." --- 5. Ackermann(3,6) verify=509: " 3 5 ack . cr
  ['] ack-once 10 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ 6. Bubble sort
\ ----------------------------------------------------------------
20 constant sort-size
create sort-buf sort-size cells allot

: sort-addr ( i -- addr ) cells sort-buf + ;

: sort-init ( -- )
  sort-size 0 do sort-size i - i sort-addr ! loop ;

: sort-run ( -- )
  sort-size 1 do
    sort-size 1 do
      i sort-addr @  i 1- sort-addr @
      2dup > if
        i sort-addr !  i 1- sort-addr !
      else
        2drop
      then
    loop
  loop ;

: sort-once ( -- ) sort-init sort-run ;

: do-bench-sort ( -- )
  ." --- 6. Bubblesort(20) verify=1 20: "
  sort-init sort-run
  0 sort-addr @ .  19 sort-addr @ . cr
  ['] sort-once 10000 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ 7. Variable read/write
\ ----------------------------------------------------------------
variable bench-var

: var-once ( -- ) 42 bench-var ! bench-var @ drop ;

: do-bench-varloop ( -- )
  ." --- 7. Var read/write x1M ---" cr
  ['] var-once 1000000 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ 8. Arithmetic throughput
\ ----------------------------------------------------------------
: arith-once ( -- ) 1 2 + 3 * 4 - 5 mod drop ;

: do-bench-arith ( -- )
  ." --- 8. Arithmetic x1M ---" cr
  ['] arith-once 1000000 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ 9. Word calls
\ ----------------------------------------------------------------
: add3 ( a b c -- n ) + + ;
: call-once ( -- ) 1 2 3 add3 drop ;

: do-bench-calls ( -- )
  ." --- 9. Word calls x1M ---" cr
  ['] call-once 1000000 bench-loop
  bench-done ;

\ ----------------------------------------------------------------
\ Run all
\ ----------------------------------------------------------------
: run-benchmarks
  bench-header
  do-bench-empty-loop  cr
  do-bench-fib         cr
  do-bench-sum         cr
  do-bench-sieve       cr
  do-bench-ack         cr
  do-bench-sort        cr
  do-bench-varloop     cr
  do-bench-arith       cr
  do-bench-calls       cr
  ." ==============================" cr
  ." Done." cr ;

run-benchmarks
bye
