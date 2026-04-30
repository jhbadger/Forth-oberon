32000000 constant sieve-size
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

: print-primes ( -- )
  0 sieve-size 0 do
    sieve-buf i + c@ if
      i 8 u.r cr then 
  loop ;

sieve
print-primes
bye
