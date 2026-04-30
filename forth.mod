MODULE Forth;
IMPORT In, Out, Strings, Files, Args, History, OS;

CONST
  STACK_SIZE  = 1024;
  CALL_DEPTH  = 512;
  HEAP_SIZE   = 67108864;  (* 64 MB *)
  POOL_SIZE   = 32768;
  STR_POOL    = 2048;
  STR_LEN     = 256;
  NAME_LEN    = 64;
  MAX_ENTRIES = 512;
  PROG_SIZE   = 4096;
  MAX_LOCALS  = 16;
  MAX_CSTACK  = 256;
  MAX_LEAVE   = 512;
  LEAVE_DEPTH = 64;
  MAX_LFRAMES = 32;
  MAX_MARKERS = 32;
  MAX_HELP    = 256;
  CELL        = 4;

  EKPRIM = 0; EKWORD = 1; EKDEFINING = 2; EKCREATE = 3;

  OP_ADD = 0; OP_SUB = 1; OP_MUL = 2; OP_DIV = 3;
  OP_MOD = 4; OP_DUP = 5; OP_DROP = 6; OP_SWAP = 7;
  OP_OVER = 8; OP_ROT = 9; OP_EQ = 10; OP_LT = 11;
  OP_GT = 12; OP_ZEQ = 13; OP_TOR = 14; OP_RFROM = 15;
  OP_RAT = 16; OP_FETCH = 17; OP_STORE = 18; OP_CFETCH = 19;
  OP_CSTORE = 20; OP_LIT = 21; OP_STRLIT = 22; OP_CALL = 23;
  OP_CALLDIRECT = 24; OP_CALLPRIM = 25; OP_BRANCH = 26;
  OP_ZBRANCH = 27; OP_EXIT = 28; OP_PUSHSTR = 29;
  OP_LOCALGET = 30; OP_LOCALSET = 31; OP_LOCALSENTER = 32;
  OP_LOCALSEXIT = 33; OP_DO = 34; OP_LOOP = 35;
  OP_PLUSLOOP = 36; OP_EXECMARKER = 37;

TYPE
  PrimFn = PROCEDURE;

  Ins = RECORD
    op: INTEGER;
    ival: INTEGER;
    svalIdx: INTEGER;
  END;

  Code = RECORD
    insStart: INTEGER;
    insLen: INTEGER;
  END;

  Entry = RECORD
    kind: INTEGER;
    name: ARRAY NAME_LEN OF CHAR;
    primFn: PrimFn;
    code: Code;
    doesCode: Code;
    bodyAddr: INTEGER;
    isImmediate: BOOLEAN;
    id: INTEGER;
  END;

  Frame = RECORD
    insEnd: INTEGER;
    pc: INTEGER;
  END;

VAR
  dstack: ARRAY STACK_SIZE OF INTEGER;
  dsp: INTEGER;
  rstack: ARRAY STACK_SIZE OF INTEGER;
  rsp: INTEGER;

  heap: ARRAY HEAP_SIZE OF BYTE;
  heapTop: INTEGER;
  baseAddr: INTEGER;
  stateAddr: INTEGER;
  padAddr: INTEGER;

  gIns: ARRAY POOL_SIZE OF Ins;
  gInsLen: INTEGER;
  gStr: ARRAY STR_POOL OF ARRAY STR_LEN OF CHAR;
  gStrLen: INTEGER;

  strTab: ARRAY STR_POOL OF ARRAY STR_LEN OF CHAR;
  strTabLen: INTEGER;

  entries: ARRAY MAX_ENTRIES OF Entry;
  nEntries: INTEGER;
  nextId: INTEGER;

  progIns: ARRAY PROG_SIZE OF Ins;
  progLen: INTEGER;
  compiling: BOOLEAN;
  current: ARRAY NAME_LEN OF CHAR;
  lastWord: ARRAY NAME_LEN OF CHAR;
  doesPos: INTEGER;

  cstack: ARRAY MAX_CSTACK OF INTEGER;
  cstackTop: INTEGER;

  leaveBase: ARRAY LEAVE_DEPTH OF INTEGER;
  leaveCnt:  ARRAY LEAVE_DEPTH OF INTEGER;
  leavePatches: ARRAY MAX_LEAVE OF INTEGER;
  leaveTop: INTEGER;
  leaveTotal: INTEGER;

  localNames: ARRAY MAX_LOCALS OF ARRAY NAME_LEN OF CHAR;
  nLocals: INTEGER;

  lframes: ARRAY MAX_LFRAMES OF ARRAY MAX_LOCALS OF INTEGER;
  lframeSize: ARRAY MAX_LFRAMES OF INTEGER;
  lframesTop: INTEGER;

  callStack: ARRAY CALL_DEPTH OF Frame;
  callDepth: INTEGER;

  picBuf: ARRAY STR_LEN OF CHAR;
  picLen: INTEGER;

  errFlag: BOOLEAN;
  errMsg: ARRAY 256 OF CHAR;
  replDone: BOOLEAN;

  mName:     ARRAY MAX_MARKERS OF ARRAY NAME_LEN OF CHAR;
  mNEntries: ARRAY MAX_MARKERS OF INTEGER;
  mHeapSz:   ARRAY MAX_MARKERS OF INTEGER;
  mGInsLen:  ARRAY MAX_MARKERS OF INTEGER;
  mGStrLen:  ARRAY MAX_MARKERS OF INTEGER;
  nMarkers: INTEGER;

  helpKey: ARRAY MAX_HELP OF ARRAY NAME_LEN OF CHAR;
  helpVal: ARRAY MAX_HELP OF ARRAY STR_LEN OF CHAR;
  helpCount: INTEGER;

  tokBuf: ARRAY 1024 OF ARRAY 256 OF CHAR;
  tokCount: INTEGER;
  tokIdx: INTEGER;

  (* break mutual recursion between Process and LoadFile *)
  runLoadFile: PROCEDURE;
  loadFileName: ARRAY 256 OF CHAR;

  exeDir: ARRAY 256 OF CHAR;

(* ── Exe-relative path ────────────────────────────────────────────── *)

PROCEDURE ExePath(name: ARRAY OF CHAR; VAR path: ARRAY OF CHAR);
BEGIN
  Strings.Copy(exeDir, path);
  Strings.Append(name, path)
END ExePath;

(* ── Error ────────────────────────────────────────────────────────── *)

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN errFlag := TRUE; Strings.Copy(msg, errMsg) END Error;

(* ── Data stack ───────────────────────────────────────────────────── *)

PROCEDURE Push(v: INTEGER);
BEGIN
  IF dsp >= STACK_SIZE THEN Error("Stack overflow"); RETURN END;
  dstack[dsp] := v; INC(dsp)
END Push;

PROCEDURE Pop(): INTEGER;
BEGIN
  IF dsp <= 0 THEN Error("Stack underflow"); RETURN 0 END;
  DEC(dsp); RETURN dstack[dsp]
END Pop;

PROCEDURE RPush(v: INTEGER);
BEGIN
  IF rsp >= STACK_SIZE THEN Error("Return stack overflow"); RETURN END;
  rstack[rsp] := v; INC(rsp)
END RPush;

PROCEDURE RPop(): INTEGER;
BEGIN
  IF rsp <= 0 THEN Error("Return stack underflow"); RETURN 0 END;
  DEC(rsp); RETURN rstack[rsp]
END RPop;

(* ── Heap ─────────────────────────────────────────────────────────── *)

PROCEDURE HeapGet(a: INTEGER): INTEGER;
VAR v: INTEGER;
BEGIN
  IF (a < 0) OR (a + CELL > heapTop) THEN Error("@: bad addr"); RETURN 0 END;
  v := heap[a] + heap[a+1]*256 + heap[a+2]*65536 + heap[a+3]*16777216;
  IF v >= 2147483648 THEN v := v - 4294967296 END;
  RETURN v
END HeapGet;

PROCEDURE HeapSet(a, v: INTEGER);
VAR u: INTEGER;
BEGIN
  IF a + CELL > HEAP_SIZE THEN Error("!: bad addr"); RETURN END;
  IF a + CELL > heapTop THEN heapTop := a + CELL END;
  IF v < 0 THEN u := v + 4294967296 ELSE u := v END;
  heap[a]   := u MOD 256; u := u DIV 256;
  heap[a+1] := u MOD 256; u := u DIV 256;
  heap[a+2] := u MOD 256; u := u DIV 256;
  heap[a+3] := u MOD 256
END HeapSet;

PROCEDURE GetBase(): INTEGER;
BEGIN RETURN HeapGet(baseAddr) END GetBase;

PROCEDURE GetState(): INTEGER;
BEGIN RETURN HeapGet(stateAddr) END GetState;

PROCEDURE SetState(v: INTEGER);
BEGIN HeapSet(stateAddr, v) END SetState;

(* ── Formatting ───────────────────────────────────────────────────── *)

PROCEDURE FormatInt(n, base: INTEGER; VAR result: ARRAY OF CHAR);
VAR u: INTEGER; r: ARRAY 72 OF CHAR; len, i, j: INTEGER; neg: BOOLEAN;
    digs: ARRAY 17 OF CHAR;
BEGIN
  digs := "0123456789abcdef";
  IF n = 0 THEN result[0] := '0'; result[1] := 0X; RETURN END;
  neg := n < 0;
  IF neg THEN u := -n ELSE u := n END;
  len := 0;
  WHILE u > 0 DO
    i := u MOD base;
    r[len] := digs[i]; u := u DIV base; INC(len)
  END;
  j := 0;
  IF neg THEN result[0] := '-'; j := 1 END;
  i := len - 1;
  WHILE i >= 0 DO result[j] := r[i]; INC(j); DEC(i) END;
  result[j] := 0X
END FormatInt;

PROCEDURE TryParse(t: ARRAY OF CHAR; VAR n: INTEGER): BOOLEAN;
VAR s: ARRAY STR_LEN OF CHAR; i, d, base: INTEGER; neg: BOOLEAN;
BEGIN
  base := GetBase();
  Strings.Copy(t, s); Strings.ToLower(s);
  i := 0; neg := (s[0] = '-');
  IF neg THEN INC(i) END;
  IF s[i] = 0X THEN RETURN FALSE END;
  n := 0;
  WHILE s[i] # 0X DO
    IF (s[i] >= '0') & (s[i] <= '9') THEN d := ORD(s[i]) - ORD('0')
    ELSIF (s[i] >= 'a') & (s[i] <= 'f') THEN d := ORD(s[i]) - ORD('a') + 10
    ELSE RETURN FALSE
    END;
    IF d >= base THEN RETURN FALSE END;
    n := n * base + d; INC(i)
  END;
  IF neg THEN n := -n END;
  RETURN TRUE
END TryParse;

(* ── Dictionary ───────────────────────────────────────────────────── *)

PROCEDURE FindEntry(name: ARRAY OF CHAR): INTEGER;
VAR i: INTEGER; lname: ARRAY NAME_LEN OF CHAR;
BEGIN
  Strings.Copy(name, lname); Strings.ToLower(lname);
  i := nEntries - 1;
  WHILE i >= 0 DO
    IF Strings.Compare(entries[i].name, lname) = 0 THEN RETURN i END;
    DEC(i)
  END;
  RETURN -1
END FindEntry;

PROCEDURE RegisterEntry(name: ARRAY OF CHAR; VAR e: Entry): INTEGER;
VAR idx: INTEGER; lname: ARRAY NAME_LEN OF CHAR;
BEGIN
  Strings.Copy(name, lname); Strings.ToLower(lname);
  e.id := nextId; INC(nextId);
  Strings.Copy(lname, e.name);
  idx := FindEntry(lname);
  IF idx >= 0 THEN entries[idx] := e; RETURN idx END;
  IF nEntries >= MAX_ENTRIES THEN Error("Dictionary full"); RETURN -1 END;
  idx := nEntries; INC(nEntries);
  entries[idx] := e;
  RETURN idx
END RegisterEntry;

PROCEDURE XtToIdx(id: INTEGER): INTEGER;
VAR i: INTEGER;
BEGIN
  i := nEntries - 1;
  WHILE i >= 0 DO
    IF entries[i].id = id THEN RETURN i END;
    DEC(i)
  END;
  Error("execute: bad xt"); RETURN -1
END XtToIdx;

(* ── Compilation ──────────────────────────────────────────────────── *)

PROCEDURE Emit(op, ival: INTEGER): INTEGER;
BEGIN
  IF progLen >= PROG_SIZE THEN Error("Word too long"); RETURN -1 END;
  progIns[progLen].op := op; progIns[progLen].ival := ival;
  progIns[progLen].svalIdx := -1; INC(progLen);
  RETURN progLen - 1
END Emit;

PROCEDURE EmitS(op, ival: INTEGER; s: ARRAY OF CHAR): INTEGER;
VAR sIdx: INTEGER;
BEGIN
  IF progLen >= PROG_SIZE THEN Error("Word too long"); RETURN -1 END;
  IF gStrLen >= STR_POOL THEN Error("String pool full"); RETURN -1 END;
  Strings.Copy(s, gStr[gStrLen]); sIdx := gStrLen; INC(gStrLen);
  progIns[progLen].op := op; progIns[progLen].ival := ival;
  progIns[progLen].svalIdx := sIdx; INC(progLen);
  RETURN progLen - 1
END EmitS;

PROCEDURE CommitCode(VAR code: Code);
VAR i, insBase: INTEGER;
BEGIN
  insBase := gInsLen;
  FOR i := 0 TO progLen - 1 DO
    IF gInsLen >= POOL_SIZE THEN Error("Code pool full"); RETURN END;
    gIns[gInsLen] := progIns[i];
    IF (gIns[gInsLen].op = OP_BRANCH) OR (gIns[gInsLen].op = OP_ZBRANCH) OR
       (gIns[gInsLen].op = OP_LOOP)   OR (gIns[gInsLen].op = OP_PLUSLOOP) THEN
      INC(gIns[gInsLen].ival, insBase)
    END;
    INC(gInsLen)
  END;
  code.insStart := insBase; code.insLen := progLen
END CommitCode;

PROCEDURE ResolveCalls(VAR code: Code);
VAR i, idx: INTEGER; nm: ARRAY NAME_LEN OF CHAR;
BEGIN
  FOR i := code.insStart TO code.insStart + code.insLen - 1 DO
    IF gIns[i].op = OP_CALL THEN
      IF gIns[i].svalIdx >= 0 THEN
        Strings.Copy(gStr[gIns[i].svalIdx], nm);
        IF    Strings.Compare(nm, "+")    = 0 THEN gIns[i].op := OP_ADD;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "-")    = 0 THEN gIns[i].op := OP_SUB;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "*")    = 0 THEN gIns[i].op := OP_MUL;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "/")    = 0 THEN gIns[i].op := OP_DIV;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "mod")  = 0 THEN gIns[i].op := OP_MOD;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "dup")  = 0 THEN gIns[i].op := OP_DUP;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "drop") = 0 THEN gIns[i].op := OP_DROP;   gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "swap") = 0 THEN gIns[i].op := OP_SWAP;   gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "over") = 0 THEN gIns[i].op := OP_OVER;   gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "rot")  = 0 THEN gIns[i].op := OP_ROT;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "=")    = 0 THEN gIns[i].op := OP_EQ;     gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "<")    = 0 THEN gIns[i].op := OP_LT;     gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, ">")    = 0 THEN gIns[i].op := OP_GT;     gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "0=")   = 0 THEN gIns[i].op := OP_ZEQ;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, ">r")   = 0 THEN gIns[i].op := OP_TOR;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "r>")   = 0 THEN gIns[i].op := OP_RFROM;  gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "r@")   = 0 THEN gIns[i].op := OP_RAT;    gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "@")    = 0 THEN gIns[i].op := OP_FETCH;  gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "!")    = 0 THEN gIns[i].op := OP_STORE;  gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "c@")   = 0 THEN gIns[i].op := OP_CFETCH; gIns[i].svalIdx := -1
        ELSIF Strings.Compare(nm, "c!")   = 0 THEN gIns[i].op := OP_CSTORE; gIns[i].svalIdx := -1
        ELSE
          idx := FindEntry(nm);
          IF idx >= 0 THEN
            IF entries[idx].kind = EKPRIM THEN gIns[i].op := OP_CALLPRIM; gIns[i].ival := idx
            ELSE                               gIns[i].op := OP_CALLDIRECT; gIns[i].ival := idx
            END
          END
        END
      END
    END
  END
END ResolveCalls;

(* ── Run loop ─────────────────────────────────────────────────────── *)

PROCEDURE RunUntil(targetDepth: INTEGER);
VAR top, idx, a, b, c, v, s, l, step: INTEGER; ins: Ins;
BEGIN
  WHILE (callDepth > targetDepth) & ~errFlag DO
    top := callDepth - 1;
    IF callStack[top].pc >= callStack[top].insEnd THEN
      DEC(callDepth)
    ELSE
      ins := gIns[callStack[top].pc];
      INC(callStack[top].pc);
      CASE ins.op OF
        OP_ADD:  b := Pop(); a := Pop(); Push(a + b)
      | OP_SUB:  b := Pop(); a := Pop(); Push(a - b)
      | OP_MUL:  b := Pop(); a := Pop(); Push(a * b)
      | OP_DIV:
          b := Pop(); a := Pop();
          IF b = 0 THEN Error("Division by zero") ELSE Push(a DIV b) END
      | OP_MOD:
          b := Pop(); a := Pop();
          IF b = 0 THEN Error("Division by zero") ELSE Push(a MOD b) END
      | OP_DUP:
          IF dsp = 0 THEN Error("dup: underflow") ELSE Push(dstack[dsp-1]) END
      | OP_DROP: a := Pop()
      | OP_SWAP: b := Pop(); a := Pop(); Push(b); Push(a)
      | OP_OVER:
          IF dsp < 2 THEN Error("over: underflow") ELSE Push(dstack[dsp-2]) END
      | OP_ROT:  c := Pop(); b := Pop(); a := Pop(); Push(b); Push(c); Push(a)
      | OP_EQ:   b := Pop(); a := Pop(); IF a = b THEN Push(-1) ELSE Push(0) END
      | OP_LT:   b := Pop(); a := Pop(); IF a < b THEN Push(-1) ELSE Push(0) END
      | OP_GT:   b := Pop(); a := Pop(); IF a > b THEN Push(-1) ELSE Push(0) END
      | OP_ZEQ:  a := Pop(); IF a = 0 THEN Push(-1) ELSE Push(0) END
      | OP_TOR:  RPush(Pop())
      | OP_RFROM: Push(RPop())
      | OP_RAT:
          IF rsp = 0 THEN Error("r@: empty") ELSE Push(rstack[rsp-1]) END
      | OP_FETCH: a := Pop(); Push(HeapGet(a))
      | OP_STORE: a := Pop(); v := Pop(); HeapSet(a, v)
      | OP_CFETCH:
          a := Pop();
          IF (a < 0) OR (a >= heapTop) THEN Error("c@: bad addr")
          ELSE Push(heap[a]) END
      | OP_CSTORE:
          a := Pop(); v := Pop();
          IF (a < 0) OR (a >= HEAP_SIZE) THEN Error("c!: bad addr")
          ELSE
            heap[a] := v MOD 256;
            IF a >= heapTop THEN heapTop := a + 1 END
          END
      | OP_LIT: Push(ins.ival)
      | OP_STRLIT:
          IF ins.svalIdx >= 0 THEN Out.String(gStr[ins.svalIdx]) END
      | OP_CALL:
          IF ins.svalIdx >= 0 THEN
            idx := FindEntry(gStr[ins.svalIdx]);
            IF idx < 0 THEN Error("Unknown word")
            ELSE
              (* patch to CALLDIRECT for future executions *)
              gIns[callStack[top].pc - 1].op := OP_CALLDIRECT;
              gIns[callStack[top].pc - 1].ival := idx;
              (* now execute it *)
              IF entries[idx].kind = EKPRIM THEN
                entries[idx].primFn()
              ELSIF entries[idx].kind = EKWORD THEN
                IF entries[idx].code.insLen > 0 THEN
                  IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow")
                  ELSE
                    callStack[callDepth].pc := entries[idx].code.insStart;
                    callStack[callDepth].insEnd := entries[idx].code.insStart + entries[idx].code.insLen;
                    INC(callDepth)
                  END
                END
              ELSIF entries[idx].kind = EKCREATE THEN
                Push(entries[idx].bodyAddr);
                IF entries[idx].doesCode.insLen > 0 THEN
                  IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow")
                  ELSE
                    callStack[callDepth].pc := entries[idx].doesCode.insStart;
                    callStack[callDepth].insEnd := entries[idx].doesCode.insStart + entries[idx].doesCode.insLen;
                    INC(callDepth)
                  END
                END
              END
            END
          ELSE Error("OP_CALL: no name") END
      | OP_CALLDIRECT:
          idx := ins.ival;
          IF entries[idx].kind = EKPRIM THEN
            entries[idx].primFn()
          ELSIF entries[idx].kind = EKWORD THEN
            IF entries[idx].code.insLen > 0 THEN
              IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow")
              ELSE
                callStack[callDepth].pc := entries[idx].code.insStart;
                callStack[callDepth].insEnd := entries[idx].code.insStart + entries[idx].code.insLen;
                INC(callDepth)
              END
            END
          ELSIF entries[idx].kind = EKCREATE THEN
            Push(entries[idx].bodyAddr);
            IF entries[idx].doesCode.insLen > 0 THEN
              IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow")
              ELSE
                callStack[callDepth].pc := entries[idx].doesCode.insStart;
                callStack[callDepth].insEnd := entries[idx].doesCode.insStart + entries[idx].doesCode.insLen;
                INC(callDepth)
              END
            END
          END
      | OP_CALLPRIM: entries[ins.ival].primFn()
      | OP_BRANCH: callStack[top].pc := ins.ival
      | OP_ZBRANCH: a := Pop(); IF a = 0 THEN callStack[top].pc := ins.ival END
      | OP_EXIT: DEC(callDepth)
      | OP_PUSHSTR:
          IF ins.svalIdx >= 0 THEN
            IF strTabLen >= STR_POOL THEN Error("String table full")
            ELSE
              Strings.Copy(gStr[ins.svalIdx], strTab[strTabLen]);
              Push(strTabLen); INC(strTabLen)
            END
          END
      | OP_LOCALGET:
          IF lframesTop > 0 THEN Push(lframes[lframesTop-1][ins.ival])
          ELSE Error("local get: no frame") END
      | OP_LOCALSET:
          IF lframesTop > 0 THEN lframes[lframesTop-1][ins.ival] := Pop()
          ELSE Error("local set: no frame") END
      | OP_LOCALSENTER:
          IF lframesTop >= MAX_LFRAMES THEN Error("Too many local frames")
          ELSE
            lframeSize[lframesTop] := ins.ival;
            FOR a := 0 TO ins.ival - 1 DO lframes[lframesTop][a] := 0 END;
            INC(lframesTop)
          END
      | OP_LOCALSEXIT:
          IF lframesTop > 0 THEN DEC(lframesTop) END
      | OP_DO:
          s := Pop(); l := Pop(); RPush(l); RPush(s)
      | OP_LOOP:
          idx := rstack[rsp-1]; DEC(rsp);
          l := rstack[rsp-1];
          INC(idx);
          IF idx < l THEN RPush(idx); callStack[top].pc := ins.ival
          ELSE DEC(rsp) END
      | OP_PLUSLOOP:
          step := Pop(); idx := rstack[rsp-1]; DEC(rsp);
          l := rstack[rsp-1];
          idx := idx + step;
          IF ((step > 0) & (idx < l)) OR ((step < 0) & (idx >= l)) THEN
            rstack[rsp-1] := l; RPush(idx); callStack[top].pc := ins.ival
          ELSE DEC(rsp) END
      | OP_EXECMARKER:
          idx := ins.ival;
          IF (idx >= 0) & (idx < nMarkers) THEN
            nEntries := mNEntries[idx];
            heapTop  := mHeapSz[idx];
            gInsLen  := mGInsLen[idx];
            gStrLen  := mGStrLen[idx];
            DEC(callDepth)
          ELSE Error("marker: not found") END
      ELSE (* unknown op *)
      END
    END
  END
END RunUntil;

PROCEDURE RunEntry(idx: INTEGER);
BEGIN
  IF (idx < 0) OR (idx >= nEntries) THEN Error("Bad entry"); RETURN END;
  IF entries[idx].kind = EKPRIM THEN
    entries[idx].primFn()
  ELSIF entries[idx].kind = EKWORD THEN
    IF entries[idx].code.insLen > 0 THEN
      IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow"); RETURN END;
      callStack[callDepth].pc := entries[idx].code.insStart;
      callStack[callDepth].insEnd := entries[idx].code.insStart + entries[idx].code.insLen;
      INC(callDepth);
      RunUntil(callDepth - 1)
    END
  ELSIF entries[idx].kind = EKCREATE THEN
    Push(entries[idx].bodyAddr);
    IF entries[idx].doesCode.insLen > 0 THEN
      IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow"); RETURN END;
      callStack[callDepth].pc := entries[idx].doesCode.insStart;
      callStack[callDepth].insEnd := entries[idx].doesCode.insStart + entries[idx].doesCode.insLen;
      INC(callDepth);
      RunUntil(callDepth - 1)
    END
  ELSIF entries[idx].kind = EKDEFINING THEN
    (* run the defining word's code part (before does>) *)
    IF entries[idx].code.insLen > 0 THEN
      IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow"); RETURN END;
      callStack[callDepth].pc := entries[idx].code.insStart;
      callStack[callDepth].insEnd := entries[idx].code.insStart + entries[idx].code.insLen;
      INC(callDepth);
      RunUntil(callDepth - 1)
    END
  END
END RunEntry;

(* ── Primitives ───────────────────────────────────────────────────── *)

(* Bitwise operations implemented via bit-by-bit calculation *)

PROCEDURE BitAnd(a, b: INTEGER): INTEGER;
VAR i, r, bit: INTEGER;
BEGIN
  r := 0; bit := 1; i := 0;
  WHILE i < 32 DO
    IF (a MOD 2 = 1) & (b MOD 2 = 1) THEN r := r + bit END;
    a := a DIV 2; b := b DIV 2; bit := bit * 2; INC(i)
  END;
  RETURN r
END BitAnd;

PROCEDURE BitOr(a, b: INTEGER): INTEGER;
VAR i, r, bit: INTEGER;
BEGIN
  r := 0; bit := 1; i := 0;
  WHILE i < 32 DO
    IF (a MOD 2 = 1) OR (b MOD 2 = 1) THEN r := r + bit END;
    a := a DIV 2; b := b DIV 2; bit := bit * 2; INC(i)
  END;
  RETURN r
END BitOr;

PROCEDURE BitXor(a, b: INTEGER): INTEGER;
VAR i, r, bit: INTEGER;
BEGIN
  r := 0; bit := 1; i := 0;
  WHILE i < 32 DO
    IF (a MOD 2) # (b MOD 2) THEN r := r + bit END;
    a := a DIV 2; b := b DIV 2; bit := bit * 2; INC(i)
  END;
  RETURN r
END BitXor;

PROCEDURE BitNot(a: INTEGER): INTEGER;
BEGIN
  (* 32-bit invert *)
  RETURN BitXor(a, -1)
END BitNot;

PROCEDURE BitLsh(a, n: INTEGER): INTEGER;
VAR i: INTEGER;
BEGIN FOR i := 0 TO n-1 DO a := a * 2 END; RETURN a END BitLsh;

PROCEDURE BitRsh(a, n: INTEGER): INTEGER;
VAR i: INTEGER; u: INTEGER;
BEGIN
  IF a < 0 THEN u := a + 4294967296 ELSE u := a END;
  FOR i := 0 TO n-1 DO u := u DIV 2 END;
  RETURN u
END BitRsh;

PROCEDURE PfPlus;   VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(a + b) END PfPlus;
PROCEDURE PfMinus;  VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(a - b) END PfMinus;
PROCEDURE PfMul;    VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(a * b) END PfMul;
PROCEDURE PfDiv;    VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); IF b = 0 THEN Error("div by zero") ELSE Push(a DIV b) END END PfDiv;
PROCEDURE PfMod;    VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); IF b = 0 THEN Error("div by zero") ELSE Push(a MOD b) END END PfMod;
PROCEDURE PfDup2;   BEGIN IF dsp = 0 THEN Error("dup: underflow") ELSE Push(dstack[dsp-1]) END END PfDup2;
PROCEDURE PfDrop2;  VAR n: INTEGER; BEGIN n := Pop() END PfDrop2;
PROCEDURE PfSwap2;  VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(b); Push(a) END PfSwap2;
PROCEDURE PfOver2;  BEGIN IF dsp < 2 THEN Error("over: underflow") ELSE Push(dstack[dsp-2]) END END PfOver2;
PROCEDURE PfRot2;   VAR c, b, a: INTEGER; BEGIN c := Pop(); b := Pop(); a := Pop(); Push(b); Push(c); Push(a) END PfRot2;
PROCEDURE PfEq2;    VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); IF a = b THEN Push(-1) ELSE Push(0) END END PfEq2;
PROCEDURE PfLt2;    VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); IF a < b THEN Push(-1) ELSE Push(0) END END PfLt2;
PROCEDURE PfGt2;    VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); IF a > b THEN Push(-1) ELSE Push(0) END END PfGt2;
PROCEDURE PfZEq2;   VAR a: INTEGER; BEGIN a := Pop(); IF a = 0 THEN Push(-1) ELSE Push(0) END END PfZEq2;
PROCEDURE PfToR2;   BEGIN RPush(Pop()) END PfToR2;
PROCEDURE PfRFrom2; BEGIN Push(RPop()) END PfRFrom2;
PROCEDURE PfRAt2;   BEGIN IF rsp = 0 THEN Error("r@: empty") ELSE Push(rstack[rsp-1]) END END PfRAt2;
PROCEDURE PfFetch2; VAR a: INTEGER; BEGIN a := Pop(); Push(HeapGet(a)) END PfFetch2;
PROCEDURE PfStore2; VAR a, v: INTEGER; BEGIN a := Pop(); v := Pop(); HeapSet(a, v) END PfStore2;
PROCEDURE PfCFetch2; VAR a: INTEGER; BEGIN a := Pop(); IF (a < 0) OR (a >= heapTop) THEN Error("c@: bad") ELSE Push(heap[a]) END END PfCFetch2;
PROCEDURE PfCStore2; VAR a, v: INTEGER; BEGIN a := Pop(); v := Pop(); IF (a < 0) OR (a >= HEAP_SIZE) THEN Error("c!: bad") ELSE heap[a] := v MOD 256; IF a >= heapTop THEN heapTop := a+1 END END END PfCStore2;
PROCEDURE PfAnd2;   VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(BitAnd(a, b)) END PfAnd2;
PROCEDURE PfOr;     VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(BitOr(a, b))  END PfOr;
PROCEDURE PfXor;    VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(BitXor(a, b)) END PfXor;
PROCEDURE PfInvert; VAR a: INTEGER;    BEGIN a := Pop(); Push(BitNot(a)) END PfInvert;
PROCEDURE PfLshift; VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(BitLsh(a, b)) END PfLshift;
PROCEDURE PfRshift; VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); Push(BitRsh(a, b)) END PfRshift;

PROCEDURE PfDepth; BEGIN Push(dsp) END PfDepth;

PROCEDURE PfPick;
VAR n: INTEGER;
BEGIN
  n := Pop();
  IF (n < 0) OR (n >= dsp) THEN Error("pick: range") ELSE Push(dstack[dsp-1-n]) END
END PfPick;

PROCEDURE PfRoll;
VAR n, val, i: INTEGER;
BEGIN
  n := Pop();
  IF (n < 0) OR (n >= dsp) THEN Error("roll: range"); RETURN END;
  val := dstack[dsp-1-n];
  FOR i := dsp-1-n TO dsp-2 DO dstack[i] := dstack[i+1] END;
  DEC(dsp); Push(val)
END PfRoll;

PROCEDURE PfDot;
VAR s: ARRAY 64 OF CHAR;
BEGIN FormatInt(Pop(), GetBase(), s); Out.String(s); Out.Char(' ') END PfDot;

PROCEDURE PfEmit;  VAR c: INTEGER; BEGIN c := Pop(); Out.Char(CHR(c MOD 256)) END PfEmit;
PROCEDURE PfCr;    BEGIN Out.Ln END PfCr;

PROCEDURE PfAtXy;
VAR y, x: INTEGER;
BEGIN
  y := Pop(); x := Pop();
  Out.Char(1BX); Out.Char('[');
  Out.Int(y+1, 0); Out.Char(';'); Out.Int(x+1, 0); Out.Char('H')
END PfAtXy;

PROCEDURE PfDots;
VAR i: INTEGER;
BEGIN
  Out.String("Stack: [");
  FOR i := 0 TO dsp-1 DO
    IF i > 0 THEN Out.String(", ") END;
    Out.Int(dstack[i], 0)
  END;
  Out.Char(']'); Out.Ln
END PfDots;

PROCEDURE PfType;
VAR i: INTEGER;
BEGIN
  i := Pop();
  IF (i < 0) OR (i >= strTabLen) THEN Error("type: bad idx") ELSE Out.String(strTab[i]) END
END PfType;

PROCEDURE PfSEq;
VAR b, a: INTEGER;
BEGIN
  b := Pop(); a := Pop();
  IF (a < 0) OR (a >= strTabLen) OR (b < 0) OR (b >= strTabLen) THEN
    Error("s=: bad idx")
  ELSIF Strings.Compare(strTab[a], strTab[b]) = 0 THEN Push(-1)
  ELSE Push(0) END
END PfSEq;

PROCEDURE PfSPlus;
VAR b, a: INTEGER; s: ARRAY STR_LEN OF CHAR;
BEGIN
  b := Pop(); a := Pop();
  IF (a < 0) OR (a >= strTabLen) OR (b < 0) OR (b >= strTabLen) THEN
    Error("s+: bad idx"); RETURN
  END;
  Strings.Copy(strTab[a], s); Strings.Append(strTab[b], s);
  IF strTabLen >= STR_POOL THEN Error("String table full"); RETURN END;
  Strings.Copy(s, strTab[strTabLen]); Push(strTabLen); INC(strTabLen)
END PfSPlus;

PROCEDURE PfSClear; BEGIN strTabLen := 0 END PfSClear;

PROCEDURE PfSDs;
VAR i: INTEGER;
BEGIN
  Out.String("String table ("); Out.Int(strTabLen, 0); Out.String("):"); Out.Ln;
  FOR i := 0 TO strTabLen-1 DO
    Out.Char('['); Out.Int(i, 0); Out.String('] "'); Out.String(strTab[i]); Out.String('"'); Out.Ln
  END
END PfSDs;

PROCEDURE PfAccept;
VAR mx, i: INTEGER; c: CHAR;
BEGIN
  mx := Pop(); i := 0;
  LOOP
    In.Read(c);
    IF (c = 0AX) OR (c = 0DX) OR (c = 0FFX) THEN EXIT END;
    IF i < STR_LEN-1 THEN
      IF strTabLen < STR_POOL THEN strTab[strTabLen][i] := c END; INC(i)
    END
  END;
  IF strTabLen < STR_POOL THEN
    IF i > mx THEN i := mx END;
    strTab[strTabLen][i] := 0X;
    Push(strTabLen); INC(strTabLen)
  ELSE Error("String table full") END
END PfAccept;

PROCEDURE PfKey;
VAR c: CHAR;
BEGIN In.Read(c); Push(ORD(c)) END PfKey;

PROCEDURE PfBase;  BEGIN Push(baseAddr) END PfBase;
PROCEDURE PfHex;   BEGIN HeapSet(baseAddr, 16) END PfHex;
PROCEDURE PfDec;   BEGIN HeapSet(baseAddr, 10) END PfDec;
PROCEDURE PfOct;   BEGIN HeapSet(baseAddr, 8)  END PfOct;
PROCEDURE PfBin;   BEGIN HeapSet(baseAddr, 2)  END PfBin;
PROCEDURE PfCellSz; BEGIN Push(CELL) END PfCellSz;
PROCEDURE PfCellP;  BEGIN Push(Pop() + CELL) END PfCellP;
PROCEDURE PfCells;  BEGIN Push(Pop() * CELL) END PfCells;

PROCEDURE PfComma;
VAR x: INTEGER;
BEGIN
  x := Pop();
  HeapSet(heapTop, x); (* HeapSet extends heapTop *)
END PfComma;

PROCEDURE PfCComma;
VAR v: INTEGER;
BEGIN
  IF heapTop >= HEAP_SIZE THEN Error("heap full"); RETURN END;
  v := Pop(); heap[heapTop] := v MOD 256; INC(heapTop)
END PfCComma;

PROCEDURE PfHere;  BEGIN Push(heapTop) END PfHere;

PROCEDURE PfAllot;
VAR n: INTEGER;
BEGIN
  n := Pop();
  IF n < 0 THEN Error("allot: negative"); RETURN END;
  IF heapTop + n > HEAP_SIZE THEN Error("allot: out of memory"); RETURN END;
  INC(heapTop, n)
END PfAllot;

PROCEDURE PfFill;
VAR u, len, a, i: INTEGER;
BEGIN
  u := Pop(); u := u MOD 256; len := Pop(); a := Pop();
  IF (a < 0) OR (a + len > heapTop) THEN Error("fill: range"); RETURN END;
  FOR i := a TO a + len - 1 DO heap[i] := u END
END PfFill;

PROCEDURE PfErase;
VAR n, a, i: INTEGER;
BEGIN
  n := Pop(); a := Pop();
  IF (n < 0) OR (a < 0) OR (a + n > heapTop) THEN Error("erase: range"); RETURN END;
  FOR i := a TO a + n - 1 DO heap[i] := 0 END
END PfErase;

PROCEDURE PfBlank;
VAR n, a, i: INTEGER;
BEGIN
  n := Pop(); a := Pop();
  IF (n < 0) OR (a < 0) OR (a + n > heapTop) THEN Error("blank: range"); RETURN END;
  FOR i := a TO a + n - 1 DO heap[i] := 32 END
END PfBlank;

PROCEDURE PfDump;
VAR len, a, i: INTEGER;
BEGIN
  len := Pop(); a := Pop();
  Out.Int(a, 0); Out.String(" :");
  FOR i := a TO a + len - 1 DO
    IF (i < 0) OR (i >= heapTop) THEN Error("dump: range"); RETURN END;
    Out.Char(' '); Out.Int(heap[i], 0)
  END;
  Out.Ln
END PfDump;

PROCEDURE PfState; BEGIN Push(stateAddr) END PfState;

PROCEDURE PfImm;
VAR idx: INTEGER;
BEGIN
  idx := FindEntry(lastWord);
  IF idx >= 0 THEN entries[idx].isImmediate := TRUE END
END PfImm;

PROCEDURE PfExecute;
VAR id, idx, savedDepth: INTEGER;
BEGIN
  id := Pop(); idx := XtToIdx(id);
  IF idx < 0 THEN RETURN END;
  savedDepth := callDepth;
  IF entries[idx].kind = EKPRIM THEN
    entries[idx].primFn()
  ELSIF entries[idx].kind = EKWORD THEN
    IF entries[idx].code.insLen > 0 THEN
      IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow"); RETURN END;
      callStack[callDepth].pc := entries[idx].code.insStart;
      callStack[callDepth].insEnd := entries[idx].code.insStart + entries[idx].code.insLen;
      INC(callDepth);
      RunUntil(savedDepth)
    END
  ELSIF entries[idx].kind = EKCREATE THEN
    Push(entries[idx].bodyAddr);
    IF entries[idx].doesCode.insLen > 0 THEN
      IF callDepth >= CALL_DEPTH THEN Error("Call stack overflow"); RETURN END;
      callStack[callDepth].pc := entries[idx].doesCode.insStart;
      callStack[callDepth].insEnd := entries[idx].doesCode.insStart + entries[idx].doesCode.insLen;
      INC(callDepth);
      RunUntil(savedDepth)
    END
  END
END PfExecute;

PROCEDURE PfCompileComma;
VAR id, idx: INTEGER;
BEGIN
  id := Pop(); idx := XtToIdx(id);
  IF idx < 0 THEN RETURN END;
  IF entries[idx].kind = EKPRIM THEN
    progIns[progLen].op := OP_CALLPRIM;
    progIns[progLen].ival := idx;
    progIns[progLen].svalIdx := -1; INC(progLen)
  ELSE
    progIns[progLen].op := OP_CALLDIRECT;
    progIns[progLen].ival := idx;
    progIns[progLen].svalIdx := -1; INC(progLen)
  END
END PfCompileComma;

PROCEDURE PfBye; BEGIN replDone := TRUE END PfBye;

PROCEDURE PfHelpSet;
VAR ki, vi: INTEGER;
BEGIN
  vi := Pop(); ki := Pop();
  IF (ki < 0) OR (ki >= strTabLen) OR (vi < 0) OR (vi >= strTabLen) THEN
    Error("help-set: bad index"); RETURN
  END;
  IF helpCount >= MAX_HELP THEN Error("help table full"); RETURN END;
  Strings.Copy(strTab[ki], helpKey[helpCount]);
  Strings.Copy(strTab[vi], helpVal[helpCount]);
  INC(helpCount)
END PfHelpSet;

PROCEDURE PfWords;
VAR i: INTEGER;
BEGIN
  FOR i := 0 TO nEntries-1 DO
    Out.String(entries[i].name); Out.Char(' ')
  END;
  Out.Ln
END PfWords;

PROCEDURE PfToBody;
VAR id, idx: INTEGER;
BEGIN
  id := Pop(); idx := XtToIdx(id);
  IF idx < 0 THEN RETURN END;
  IF entries[idx].kind # EKCREATE THEN Error(">body: not a CREATE word"); RETURN END;
  Push(entries[idx].bodyAddr)
END PfToBody;

PROCEDURE PfBodyFrom;
VAR ba, i: INTEGER;
BEGIN
  ba := Pop();
  i := 0;
  WHILE i < nEntries DO
    IF (entries[i].kind = EKCREATE) & (entries[i].bodyAddr = ba) THEN
      Push(entries[i].id); RETURN
    END;
    INC(i)
  END;
  Error("body>: no entry found")
END PfBodyFrom;

PROCEDURE PfSlashMod;
VAR b, a: INTEGER;
BEGIN
  b := Pop(); a := Pop();
  IF b = 0 THEN Error("/mod: div by zero"); RETURN END;
  Push(a MOD b); Push(a DIV b)
END PfSlashMod;

PROCEDURE PfStarSlash;
VAR c, b, a: INTEGER;
BEGIN
  c := Pop(); b := Pop(); a := Pop();
  IF c = 0 THEN Error("*/: div by zero"); RETURN END;
  Push((a * b) DIV c)
END PfStarSlash;

PROCEDURE PfStarSlashMod;
VAR c, b, a, p: INTEGER;
BEGIN
  c := Pop(); b := Pop(); a := Pop();
  IF c = 0 THEN Error("*/mod: div by zero"); RETURN END;
  p := a * b; Push(p MOD c); Push(p DIV c)
END PfStarSlashMod;

PROCEDURE PfLBracket; BEGIN SetState(0) END PfLBracket;
PROCEDURE PfRBracket; BEGIN SetState(1) END PfRBracket;

PROCEDURE PfLiteral;
BEGIN progIns[progLen].op := OP_LIT; progIns[progLen].ival := Pop();
      progIns[progLen].svalIdx := -1; INC(progLen) END PfLiteral;

PROCEDURE PfCatch;
VAR id, idx, oldDsp, oldRsp, oldCallDepth, oldLframes: INTEGER;
BEGIN
  id := Pop(); idx := XtToIdx(id);
  IF idx < 0 THEN RETURN END;
  oldDsp := dsp; oldRsp := rsp; oldCallDepth := callDepth; oldLframes := lframesTop;
  errFlag := FALSE;
  RunEntry(idx);
  IF errFlag THEN
    dsp := oldDsp; rsp := oldRsp; callDepth := oldCallDepth; lframesTop := oldLframes;
    errFlag := FALSE;
    IF strTabLen < STR_POOL THEN
      Strings.Copy(errMsg, strTab[strTabLen]); Push(strTabLen); INC(strTabLen)
    END;
    Push(-1)
  ELSE Push(0) END
END PfCatch;

PROCEDURE PfThrow;
VAR n, idx: INTEGER;
BEGIN
  n := Pop();
  IF n = 0 THEN RETURN END;
  IF (n = -1) & (dsp > 0) THEN
    idx := Pop();
    IF (idx >= 0) & (idx < strTabLen) THEN Error(strTab[idx])
    ELSE Error("error") END
  ELSE
    Strings.Copy("throw ", errMsg);
    Strings.Append("0", errMsg); (* rough *)
    errFlag := TRUE
  END
END PfThrow;

PROCEDURE PfNoop; END PfNoop;

PROCEDURE Pf2Over;
BEGIN
  IF dsp < 4 THEN Error("2over: underflow"); RETURN END;
  Push(dstack[dsp-4]); Push(dstack[dsp-3])
END Pf2Over;

PROCEDURE PfLt0; VAR a: INTEGER; BEGIN a := Pop(); IF a < 0 THEN Push(-1) ELSE Push(0) END END PfLt0;
PROCEDURE PfGt0; VAR a: INTEGER; BEGIN a := Pop(); IF a > 0 THEN Push(-1) ELSE Push(0) END END PfGt0;
PROCEDURE PfNe0; VAR a: INTEGER; BEGIN a := Pop(); IF a # 0 THEN Push(-1) ELSE Push(0) END END PfNe0;
PROCEDURE PfNe;  VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); IF a # b THEN Push(-1) ELSE Push(0) END END PfNe;

PROCEDURE PfULt;
VAR b, a: INTEGER;
BEGIN
  b := Pop(); a := Pop();
  IF a < 0 THEN INC(a, 4294967296) END;  (* treat as unsigned *)
  IF b < 0 THEN INC(b, 4294967296) END;
  IF a < b THEN Push(-1) ELSE Push(0) END
END PfULt;

PROCEDURE PfUGt;
VAR b, a: INTEGER;
BEGIN
  b := Pop(); a := Pop();
  IF a < 0 THEN INC(a, 4294967296) END;
  IF b < 0 THEN INC(b, 4294967296) END;
  IF a > b THEN Push(-1) ELSE Push(0) END
END PfUGt;

PROCEDURE PfCharP; BEGIN Push(Pop() + 1) END PfCharP;
PROCEDURE PfChars; END PfChars;

PROCEDURE PfCount;
VAR a, n: INTEGER;
BEGIN
  a := Pop();
  IF (a < 0) OR (a >= heapTop) THEN Error("count: bad addr"); RETURN END;
  n := heap[a]; Push(a+1); Push(n)
END PfCount;

PROCEDURE PfMove;
VAR n, dst, src, i: INTEGER;
BEGIN
  n := Pop(); dst := Pop(); src := Pop();
  IF n < 0 THEN Error("move: negative"); RETURN END;
  IF (src < 0) OR (dst < 0) OR (src + n > heapTop) OR (dst + n > HEAP_SIZE) THEN
    Error("move: bad range"); RETURN
  END;
  IF dst > heapTop THEN heapTop := dst + n END;
  IF src < dst THEN
    FOR i := n-1 TO 0 BY -1 DO heap[dst+i] := heap[src+i] END
  ELSE
    FOR i := 0 TO n-1 DO heap[dst+i] := heap[src+i] END
  END
END PfMove;

PROCEDURE PfCMove;
VAR n, dst, src, i: INTEGER;
BEGIN
  n := Pop(); dst := Pop(); src := Pop();
  IF (n < 0) OR (src < 0) OR (dst < 0) OR (src+n > heapTop) OR (dst+n > HEAP_SIZE) THEN
    Error("cmove: bad"); RETURN
  END;
  IF dst + n > heapTop THEN heapTop := dst + n END;
  FOR i := 0 TO n-1 DO heap[dst+i] := heap[src+i] END
END PfCMove;

PROCEDURE PfCMoveGt;
VAR n, dst, src, i: INTEGER;
BEGIN
  n := Pop(); dst := Pop(); src := Pop();
  IF (n < 0) OR (src < 0) OR (dst < 0) OR (src+n > heapTop) OR (dst+n > HEAP_SIZE) THEN
    Error("cmove>: bad"); RETURN
  END;
  IF dst + n > heapTop THEN heapTop := dst + n END;
  FOR i := n-1 TO 0 BY -1 DO heap[dst+i] := heap[src+i] END
END PfCMoveGt;

PROCEDURE PfS2D; VAR n: INTEGER; BEGIN n := Pop(); Push(n); IF n < 0 THEN Push(-1) ELSE Push(0) END END PfS2D;
PROCEDURE PfD2S; VAR n: INTEGER; BEGIN n := Pop() END PfD2S;

PROCEDURE PfUMStar;
VAR a, b, r: INTEGER;
BEGIN
  a := Pop(); b := Pop();
  IF a < 0 THEN INC(a, 4294967296) END;
  IF b < 0 THEN INC(b, 4294967296) END;
  r := a * b;
  Push(r MOD 4294967296); Push(r DIV 4294967296)
END PfUMStar;

PROCEDURE PfUMSlashMod;
VAR divisor, hi, lo, ud, q, r: INTEGER;
BEGIN
  divisor := Pop();
  IF divisor < 0 THEN INC(divisor, 4294967296) END;
  hi := Pop(); lo := Pop();
  IF hi < 0 THEN INC(hi, 4294967296) END;
  IF lo < 0 THEN INC(lo, 4294967296) END;
  ud := hi * 4294967296 + lo;
  IF divisor = 0 THEN Error("um/mod: div by zero"); RETURN END;
  q := ud DIV divisor; r := ud MOD divisor;
  Push(r); Push(q)
END PfUMSlashMod;

PROCEDURE PfSMRem;
VAR divisor, hi, lo, d, q, r: INTEGER;
BEGIN
  divisor := Pop(); hi := Pop(); lo := Pop();
  IF lo < 0 THEN INC(lo, 4294967296) END;
  d := hi * 4294967296 + lo;
  IF divisor = 0 THEN Error("sm/rem: div by zero"); RETURN END;
  q := d DIV divisor; r := d MOD divisor;
  Push(r); Push(q)
END PfSMRem;

PROCEDURE Pf2Tor;  VAR b, a: INTEGER; BEGIN b := Pop(); a := Pop(); RPush(a); RPush(b) END Pf2Tor;
PROCEDURE Pf2RFrom; VAR b, a: INTEGER; BEGIN b := RPop(); a := RPop(); Push(a); Push(b) END Pf2RFrom;
PROCEDURE Pf2RAt;
BEGIN
  IF rsp < 2 THEN Error("2r@: underflow"); RETURN END;
  Push(rstack[rsp-2]); Push(rstack[rsp-1])
END Pf2RAt;

PROCEDURE PfUDot;
VAR u: INTEGER; s: ARRAY 64 OF CHAR;
BEGIN
  u := Pop(); IF u < 0 THEN INC(u, 4294967296) END;
  FormatInt(u, GetBase(), s); Out.String(s); Out.Char(' ')
END PfUDot;

PROCEDURE PfDotR;
VAR w, n: INTEGER; s: ARRAY 64 OF CHAR; pad, i: INTEGER;
BEGIN
  w := Pop(); n := Pop(); FormatInt(n, GetBase(), s);
  pad := w - Strings.Length(s);
  FOR i := 0 TO pad-1 DO Out.Char(' ') END;
  Out.String(s)
END PfDotR;

PROCEDURE PfUDotR;
VAR w, u: INTEGER; s: ARRAY 64 OF CHAR; pad, i: INTEGER;
BEGIN
  w := Pop(); u := Pop();
  IF u < 0 THEN INC(u, 4294967296) END;
  FormatInt(u, GetBase(), s);
  pad := w - Strings.Length(s);
  FOR i := 0 TO pad-1 DO Out.Char(' ') END;
  Out.String(s)
END PfUDotR;

PROCEDURE PfBl;    BEGIN Push(32) END PfBl;
PROCEDURE PfSpace; BEGIN Out.Char(' ') END PfSpace;
PROCEDURE PfSpaces; VAR n, i: INTEGER; BEGIN n := Pop(); FOR i := 0 TO n-1 DO Out.Char(' ') END END PfSpaces;
PROCEDURE PfPad;   BEGIN Push(padAddr) END PfPad;
PROCEDURE PfUnused; BEGIN Push(HEAP_SIZE - heapTop) END PfUnused;

PROCEDURE PfCompare;
VAR n2, a2, n1, a1, i, c1, c2: INTEGER;
BEGIN
  n2 := Pop(); a2 := Pop(); n1 := Pop(); a1 := Pop();
  i := 0;
  WHILE (i < n1) & (i < n2) DO
    c1 := heap[a1+i]; c2 := heap[a2+i];
    IF c1 < c2 THEN Push(-1); RETURN
    ELSIF c1 > c2 THEN Push(1); RETURN
    END;
    INC(i)
  END;
  IF n1 < n2 THEN Push(-1)
  ELSIF n1 > n2 THEN Push(1)
  ELSE Push(0) END
END PfCompare;

PROCEDURE PfWithin; VAR hi, lo, n: INTEGER; BEGIN hi := Pop(); lo := Pop(); n := Pop(); IF (n >= lo) & (n < hi) THEN Push(-1) ELSE Push(0) END END PfWithin;
PROCEDURE PfBounds; VAR n, a: INTEGER; BEGIN n := Pop(); a := Pop(); Push(a+n); Push(a) END PfBounds;
PROCEDURE PfAbort;  BEGIN Error("abort") END PfAbort;
PROCEDURE PfQuit;   BEGIN Error("quit") END PfQuit;

PROCEDURE PfQDup;
BEGIN
  IF dsp = 0 THEN Error("?dup: underflow"); RETURN END;
  IF dstack[dsp-1] # 0 THEN Push(dstack[dsp-1]) END
END PfQDup;

PROCEDURE Pf2Nip;
BEGIN
  IF dsp < 4 THEN Error("2nip: underflow"); RETURN END;
  dstack[dsp-4] := dstack[dsp-2]; dstack[dsp-3] := dstack[dsp-1]; DEC(dsp, 2)
END Pf2Nip;

PROCEDURE PfPicStart; BEGIN picLen := 0; picBuf[0] := 0X END PfPicStart;

PROCEDURE PfPicDigit;
VAR hi, lo, ud: INTEGER; d: INTEGER; digs: ARRAY 17 OF CHAR; s: ARRAY 2 OF CHAR;
BEGIN
  digs := "0123456789abcdef";
  hi := Pop(); lo := Pop();
  IF hi < 0 THEN INC(hi, 4294967296) END;
  IF lo < 0 THEN INC(lo, 4294967296) END;
  ud := hi * 4294967296 + lo;
  d := ud MOD GetBase();
  s[0] := digs[d]; s[1] := 0X;
  (* prepend to picBuf *)
  Strings.Append(picBuf, s); Strings.Copy(s, picBuf);
  ud := ud DIV GetBase();
  Push(ud MOD 4294967296); Push(ud DIV 4294967296)
END PfPicDigit;

PROCEDURE PfPicDigits;
VAR hi, lo, ud: INTEGER; d: INTEGER; digs: ARRAY 17 OF CHAR; s: ARRAY 2 OF CHAR;
BEGIN
  digs := "0123456789abcdef";
  hi := Pop(); lo := Pop();
  IF hi < 0 THEN INC(hi, 4294967296) END;
  IF lo < 0 THEN INC(lo, 4294967296) END;
  ud := hi * 4294967296 + lo;
  REPEAT
    d := ud MOD GetBase();
    s[0] := digs[d]; s[1] := 0X;
    Strings.Append(picBuf, s);
    ud := ud DIV GetBase()
  UNTIL ud = 0;
  Push(0); Push(0)
END PfPicDigits;

PROCEDURE PfPicSign;
VAR s: ARRAY 2 OF CHAR;
BEGIN
  IF Pop() < 0 THEN s[0] := '-'; s[1] := 0X; Strings.Append(picBuf, s) END
END PfPicSign;

PROCEDURE PfHold;
VAR s: ARRAY 2 OF CHAR; c: INTEGER;
BEGIN c := Pop(); s[0] := CHR(c MOD 256); s[1] := 0X; Strings.Append(picBuf, s) END PfHold;

PROCEDURE PfHolds;
VAR idx: INTEGER;
BEGIN
  idx := Pop();
  IF (idx >= 0) & (idx < strTabLen) THEN Strings.Append(strTab[idx], picBuf) END
END PfHolds;

PROCEDURE PfPicEnd;
BEGIN
  Pop(); Pop(); (* discard ud *)
  IF strTabLen >= STR_POOL THEN Error("String table full"); RETURN END;
  Strings.Copy(picBuf, strTab[strTabLen]);
  Push(strTabLen); Push(Strings.Length(picBuf)); INC(strTabLen)
END PfPicEnd;

PROCEDURE PfSpAt;  BEGIN Push(dsp) END PfSpAt;
PROCEDURE PfSpStore; VAR n: INTEGER; BEGIN n := Pop(); IF (n >= 0) & (n <= STACK_SIZE) THEN dsp := n ELSE Error("sp!: bad") END END PfSpStore;

PROCEDURE PfI; BEGIN IF rsp > 0 THEN Push(rstack[rsp-1]) ELSE Error("i: no loop") END END PfI;
PROCEDURE PfJ; BEGIN IF rsp >= 3 THEN Push(rstack[rsp-3]) ELSE Error("j: not in nested loop") END END PfJ;
PROCEDURE PfUnloop; BEGIN IF rsp >= 2 THEN DEC(rsp, 2) ELSE Error("unloop: not in loop") END END PfUnloop;

(* Compile-time immediates *)
PROCEDURE PfIf;
BEGIN
  progIns[progLen].op := OP_ZBRANCH; progIns[progLen].ival := 0;
  progIns[progLen].svalIdx := -1; INC(progLen);
  IF cstackTop >= MAX_CSTACK THEN Error("Control stack overflow"); RETURN END;
  cstack[cstackTop] := progLen - 1; INC(cstackTop)
END PfIf;

PROCEDURE PfElse;
VAR p: INTEGER;
BEGIN
  progIns[progLen].op := OP_BRANCH; progIns[progLen].ival := 0;
  progIns[progLen].svalIdx := -1; INC(progLen);
  IF cstackTop <= 0 THEN Error("else: no matching if"); RETURN END;
  p := cstack[cstackTop-1]; cstack[cstackTop-1] := progLen - 1;
  progIns[p].ival := progLen
END PfElse;

PROCEDURE PfThen;
VAR p: INTEGER;
BEGIN
  IF cstackTop <= 0 THEN Error("then: no matching if"); RETURN END;
  DEC(cstackTop); p := cstack[cstackTop];
  progIns[p].ival := progLen
END PfThen;

PROCEDURE PfBegin;
BEGIN
  IF cstackTop >= MAX_CSTACK THEN Error("Control stack overflow"); RETURN END;
  cstack[cstackTop] := progLen; INC(cstackTop)
END PfBegin;

PROCEDURE PfUntil;
VAR t: INTEGER;
BEGIN
  IF cstackTop <= 0 THEN Error("until: no begin"); RETURN END;
  DEC(cstackTop); t := cstack[cstackTop];
  progIns[progLen].op := OP_ZBRANCH; progIns[progLen].ival := t;
  progIns[progLen].svalIdx := -1; INC(progLen)
END PfUntil;

PROCEDURE PfAgain;
VAR t: INTEGER;
BEGIN
  IF cstackTop <= 0 THEN Error("again: no begin"); RETURN END;
  DEC(cstackTop); t := cstack[cstackTop];
  progIns[progLen].op := OP_BRANCH; progIns[progLen].ival := t;
  progIns[progLen].svalIdx := -1; INC(progLen)
END PfAgain;

PROCEDURE PfWhile;
BEGIN
  progIns[progLen].op := OP_ZBRANCH; progIns[progLen].ival := 0;
  progIns[progLen].svalIdx := -1; INC(progLen);
  IF cstackTop >= MAX_CSTACK THEN Error("Control stack overflow"); RETURN END;
  cstack[cstackTop] := progLen - 1; INC(cstackTop)
END PfWhile;

PROCEDURE PfRepeat;
VAR wa, ba: INTEGER;
BEGIN
  IF cstackTop < 2 THEN Error("repeat: no begin/while"); RETURN END;
  DEC(cstackTop); wa := cstack[cstackTop];
  DEC(cstackTop); ba := cstack[cstackTop];
  progIns[progLen].op := OP_BRANCH; progIns[progLen].ival := ba;
  progIns[progLen].svalIdx := -1; INC(progLen);
  progIns[wa].ival := progLen
END PfRepeat;

PROCEDURE PfDo;
BEGIN
  progIns[progLen].op := OP_DO; progIns[progLen].ival := 0;
  progIns[progLen].svalIdx := -1; INC(progLen);
  IF cstackTop >= MAX_CSTACK THEN Error("Control stack overflow"); RETURN END;
  cstack[cstackTop] := progLen; INC(cstackTop);
  IF leaveTop >= LEAVE_DEPTH THEN Error("Too many nested loops"); RETURN END;
  leaveBase[leaveTop] := leaveTotal; leaveCnt[leaveTop] := 0; INC(leaveTop)
END PfDo;

PROCEDURE PfQDo;
VAR zbr, skipB: INTEGER;
BEGIN
  progIns[progLen].op := OP_OVER; progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
  progIns[progLen].op := OP_OVER; progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
  progIns[progLen].op := OP_EQ;   progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
  progIns[progLen].op := OP_ZBRANCH; progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
  zbr := progLen - 1;
  progIns[progLen].op := OP_DROP; progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
  progIns[progLen].op := OP_DROP; progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
  progIns[progLen].op := OP_BRANCH; progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
  skipB := progLen - 1;
  progIns[zbr].ival := progLen;
  progIns[progLen].op := OP_DO; progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
  IF cstackTop >= MAX_CSTACK THEN Error("Control stack overflow"); RETURN END;
  cstack[cstackTop] := progLen; INC(cstackTop);
  IF leaveTop >= LEAVE_DEPTH THEN Error("Too many nested loops"); RETURN END;
  leaveBase[leaveTop] := leaveTotal;
  IF leaveTotal < MAX_LEAVE THEN
    leavePatches[leaveTotal] := skipB; leaveCnt[leaveTop] := 1; INC(leaveTotal)
  ELSE leaveCnt[leaveTop] := 0 END;
  INC(leaveTop)
END PfQDo;

PROCEDURE PfLoop;
VAR a, ea, j, p: INTEGER;
BEGIN
  IF cstackTop <= 0 THEN Error("loop: no do"); RETURN END;
  DEC(cstackTop); a := cstack[cstackTop];
  progIns[progLen].op := OP_LOOP; progIns[progLen].ival := a;
  progIns[progLen].svalIdx := -1; INC(progLen);
  ea := progLen;
  IF leaveTop > 0 THEN
    DEC(leaveTop);
    FOR j := 0 TO leaveCnt[leaveTop]-1 DO
      p := leaveBase[leaveTop] + j;
      progIns[leavePatches[p]].ival := ea
    END
  END
END PfLoop;

PROCEDURE PfPLoop;
VAR a, ea, j, p: INTEGER;
BEGIN
  IF cstackTop <= 0 THEN Error("+loop: no do"); RETURN END;
  DEC(cstackTop); a := cstack[cstackTop];
  progIns[progLen].op := OP_PLUSLOOP; progIns[progLen].ival := a;
  progIns[progLen].svalIdx := -1; INC(progLen);
  ea := progLen;
  IF leaveTop > 0 THEN
    DEC(leaveTop);
    FOR j := 0 TO leaveCnt[leaveTop]-1 DO
      p := leaveBase[leaveTop] + j;
      progIns[leavePatches[p]].ival := ea
    END
  END
END PfPLoop;

PROCEDURE PfLeave;
BEGIN
  IF leaveTop <= 0 THEN Error("leave: not in do-loop"); RETURN END;
  progIns[progLen].op := OP_BRANCH; progIns[progLen].ival := 0;
  progIns[progLen].svalIdx := -1; INC(progLen);
  IF leaveTotal < MAX_LEAVE THEN
    leavePatches[leaveTotal] := progLen - 1;
    INC(leaveCnt[leaveTop-1]); INC(leaveTotal)
  END
END PfLeave;

PROCEDURE PfRecurse;
BEGIN
  progIns[progLen].op := OP_CALL; progIns[progLen].ival := 0;
  IF gStrLen < STR_POOL THEN
    Strings.Copy(current, gStr[gStrLen]);
    progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
  END;
  INC(progLen)
END PfRecurse;

PROCEDURE PfExit;
BEGIN
  IF nLocals > 0 THEN
    progIns[progLen].op := OP_LOCALSEXIT; progIns[progLen].ival := 0;
    progIns[progLen].svalIdx := -1; INC(progLen)
  END;
  progIns[progLen].op := OP_EXIT; progIns[progLen].ival := 0;
  progIns[progLen].svalIdx := -1; INC(progLen)
END PfExit;

(* ── Tokenizer ────────────────────────────────────────────────────── *)

PROCEDURE Trim(VAR s: ARRAY OF CHAR);
VAR i, j, len: INTEGER;
BEGIN
  len := Strings.Length(s);
  i := 0;
  WHILE (i < len) & ((s[i] = ' ') OR (s[i] = 9X) OR (s[i] = 0DX) OR (s[i] = 0AX)) DO INC(i) END;
  j := 0;
  WHILE i < len DO s[j] := s[i]; INC(j); INC(i) END;
  WHILE (j > 0) & ((s[j-1] = ' ') OR (s[j-1] = 9X) OR (s[j-1] = 0DX) OR (s[j-1] = 0AX)) DO DEC(j) END;
  s[j] := 0X
END Trim;

PROCEDURE SplitStr(s: ARRAY OF CHAR);
VAR i, j, len: INTEGER;
BEGIN
  tokCount := 0; tokIdx := 0;
  len := Strings.Length(s); i := 0;
  WHILE i < len DO
    WHILE (i < len) & ((s[i] = ' ') OR (s[i] = 9X)) DO INC(i) END;
    IF i < len THEN
      j := 0;
      WHILE (i < len) & (s[i] # ' ') & (s[i] # 9X) DO
        IF j < 255 THEN tokBuf[tokCount][j] := s[i]; INC(j) END;
        INC(i)
      END;
      tokBuf[tokCount][j] := 0X;
      IF tokCount < 1023 THEN INC(tokCount) END
    END
  END
END SplitStr;

PROCEDURE CollectString(delim: CHAR; VAR result: ARRAY OF CHAR);
(* collect tokens from tokIdx until one ends with delim;
   a lone CHR(10) token (newline marker) is preserved as a literal newline *)
VAR len: INTEGER; t: ARRAY 256 OF CHAR; done: BOOLEAN;
    nl: ARRAY 2 OF CHAR;
BEGIN
  result[0] := 0X; done := FALSE;
  nl[0] := 0AX; nl[1] := 0X;
  WHILE (tokIdx < tokCount) & ~done DO
    Strings.Copy(tokBuf[tokIdx], t); INC(tokIdx);
    len := Strings.Length(t);
    IF (len = 1) & (t[0] = 0AX) THEN
      (* newline marker inserted by multiline string accumulation *)
      Strings.Append(nl, result)
    ELSE
      IF (len > 0) & (t[len-1] = delim) THEN
        t[len-1] := 0X; done := TRUE
      END;
      IF (Strings.Length(result) > 0) &
         (result[Strings.Length(result)-1] # 0AX) THEN
        Strings.Append(" ", result)
      END;
      Strings.Append(t, result)
    END
  END;
  IF ~done THEN Error("Unterminated string") END
END CollectString;

(* ── Process ──────────────────────────────────────────────────────── *)

PROCEDURE SeeCode(VAR code: Code);
VAR i: INTEGER; ins: Ins; s: ARRAY 64 OF CHAR;
BEGIN
  FOR i := code.insStart TO code.insStart + code.insLen - 1 DO
    ins := gIns[i];
    Out.String("  ");
    CASE ins.op OF
      OP_ADD:  Out.String("+")
    | OP_SUB:  Out.String("-")
    | OP_MUL:  Out.String("*")
    | OP_DIV:  Out.String("/")
    | OP_MOD:  Out.String("mod")
    | OP_DUP:  Out.String("dup")
    | OP_DROP: Out.String("drop")
    | OP_SWAP: Out.String("swap")
    | OP_OVER: Out.String("over")
    | OP_ROT:  Out.String("rot")
    | OP_EQ:   Out.String("=")
    | OP_LT:   Out.String("<")
    | OP_GT:   Out.String(">")
    | OP_ZEQ:  Out.String("0=")
    | OP_TOR:  Out.String(">r")
    | OP_RFROM: Out.String("r>")
    | OP_RAT:  Out.String("r@")
    | OP_FETCH: Out.String("@")
    | OP_STORE: Out.String("!")
    | OP_CFETCH: Out.String("c@")
    | OP_CSTORE: Out.String("c!")
    | OP_LIT:  Out.String("lit "); Out.Int(ins.ival, 0)
    | OP_STRLIT: Out.String('." ');
        IF ins.svalIdx >= 0 THEN Out.String(gStr[ins.svalIdx]) END; Out.String('"')
    | OP_CALL: Out.String("call ");
        IF ins.svalIdx >= 0 THEN Out.String(gStr[ins.svalIdx]) END
    | OP_CALLDIRECT: Out.String("call ");
        Out.String(entries[ins.ival].name)
    | OP_CALLPRIM: Out.String("prim ");
        Out.String(entries[ins.ival].name)
    | OP_BRANCH:  Out.String("branch -> "); Out.Int(ins.ival, 0)
    | OP_ZBRANCH: Out.String("0branch -> "); Out.Int(ins.ival, 0)
    | OP_EXIT:    Out.String("exit")
    | OP_PUSHSTR: Out.String('s" ');
        IF ins.svalIdx >= 0 THEN Out.String(gStr[ins.svalIdx]) END; Out.Char('"')
    | OP_DO:      Out.String("do")
    | OP_LOOP:    Out.String("loop -> "); Out.Int(ins.ival, 0)
    | OP_PLUSLOOP: Out.String("+loop -> "); Out.Int(ins.ival, 0)
    | OP_LOCALGET: Out.String("lget "); Out.Int(ins.ival, 0)
    | OP_LOCALSET: Out.String("lset "); Out.Int(ins.ival, 0)
    | OP_LOCALSENTER: Out.String("locals-enter "); Out.Int(ins.ival, 0)
    | OP_LOCALSEXIT:  Out.String("locals-exit")
    | OP_EXECMARKER:  Out.String("[marker]")
    ELSE Out.String("op"); Out.Int(ins.op, 0)
    END;
    Out.Ln
  END
END SeeCode;

PROCEDURE InitExeDir;
VAR i: INTEGER;
BEGIN
  Args.Get(0, exeDir);
  i := Strings.Length(exeDir) - 1;
  WHILE (i >= 0) & (exeDir[i] # '/') DO DEC(i) END;
  IF i >= 0 THEN exeDir[i+1] := 0X ELSE exeDir[0] := 0X END
END InitExeDir;

PROCEDURE PrintHelp(word: ARRAY OF CHAR);
VAR path: ARRAY 256 OF CHAR; f: Files.File; r: Files.Rider;
    line: ARRAY 512 OF CHAR; i: INTEGER; b: BYTE; found: BOOLEAN;
BEGIN
  (* Check dynamic help table first *)
  i := 0; found := FALSE;
  WHILE (i < helpCount) & ~found DO
    IF Strings.Compare(helpKey[i], word) = 0 THEN
      Out.String(helpVal[i]); Out.Ln;
      found := TRUE
    END;
    INC(i)
  END;
  IF found THEN RETURN END;
  (* Fall back to help.txt *)
  ExePath("help.txt", path);
  f := Files.Old(path);
  IF f = NIL THEN
    Out.String("No help for '"); Out.String(word); Out.String("'"); Out.Ln; RETURN
  END;
  Files.Set(r, f, 0);
  found := FALSE;
  LOOP
    i := 0;
    LOOP
      Files.Read(r, b);
      IF r.eof OR (b = 10) THEN EXIT END;
      IF (b # 13) & (i < 510) THEN line[i] := CHR(b); INC(i) END
    END;
    line[i] := 0X;
    IF ~found THEN
      IF Strings.Compare(line, word) = 0 THEN found := TRUE END
    ELSE
      IF Strings.Length(line) = 0 THEN EXIT END;
      Out.String(line); Out.Ln
    END;
    IF r.eof THEN EXIT END
  END;
  Files.Close(f);
  IF ~found THEN Out.String("No help for '"); Out.String(word); Out.String("'"); Out.Ln END
END PrintHelp;

PROCEDURE Process;
VAR t: ARRAY NAME_LEN OF CHAR; lw: ARRAY NAME_LEN OF CHAR;
    s: ARRAY STR_LEN OF CHAR; idx, n, i, j: INTEGER;
    e: Entry; code: Code; doesCode: Code;
    c: CHAR;
BEGIN
  WHILE (tokIdx < tokCount) & ~errFlag DO
    Strings.Copy(tokBuf[tokIdx], t); Strings.ToLower(t);
    INC(tokIdx);

    (* Line comment *)
    IF Strings.Compare(t, "\") = 0 THEN tokIdx := tokCount; (* skip rest *)

    (* Block comment *)
    ELSIF Strings.Compare(t, "(") = 0 THEN
      WHILE (tokIdx < tokCount) & (Strings.Compare(tokBuf[tokIdx], ")") # 0) DO INC(tokIdx) END;
      IF tokIdx < tokCount THEN INC(tokIdx) END;

    (* String literals *)
    ELSIF Strings.Compare(t, 's"') = 0 THEN
      CollectString('"', s);
      IF GetState() = 0 THEN
        IF strTabLen < STR_POOL THEN
          Strings.Copy(s, strTab[strTabLen]); Push(strTabLen); INC(strTabLen)
        END
      ELSE
        IF gStrLen < STR_POOL THEN
          Strings.Copy(s, gStr[gStrLen]);
          progIns[progLen].op := OP_PUSHSTR; progIns[progLen].ival := 0;
          progIns[progLen].svalIdx := gStrLen; INC(gStrLen); INC(progLen)
        END
      END;

    ELSIF (Strings.Compare(t, '."') = 0) OR (Strings.Compare(t, ".(") = 0) THEN
      IF t[1] = '(' THEN c := ')' ELSE c := '"' END;
      CollectString(c, s);
      IF GetState() = 0 THEN Out.String(s)
      ELSE
        IF gStrLen < STR_POOL THEN
          Strings.Copy(s, gStr[gStrLen]);
          progIns[progLen].op := OP_STRLIT; progIns[progLen].ival := 0;
          progIns[progLen].svalIdx := gStrLen; INC(gStrLen); INC(progLen)
        END
      END;

    ELSIF Strings.Compare(t, 'abort"') = 0 THEN
      CollectString('"', s);
      IF GetState() = 0 THEN
        IF (dsp > 0) & (Pop() # 0) THEN Error(s) END
      ELSE
        n := progLen;
        progIns[progLen].op := OP_ZBRANCH; progIns[progLen].ival := 0; progIns[progLen].svalIdx := -1; INC(progLen);
        IF gStrLen < STR_POOL THEN
          Strings.Copy(s, gStr[gStrLen]);
          progIns[progLen].op := OP_PUSHSTR; progIns[progLen].ival := 0; progIns[progLen].svalIdx := gStrLen; INC(gStrLen); INC(progLen);
          progIns[n].ival := progLen + 1;  (* skip throw if 0 *)
          progIns[progLen].op := OP_CALL; progIns[progLen].svalIdx := -1; progIns[progLen].ival := 0;
          IF gStrLen < STR_POOL THEN
            Strings.Copy("throw", gStr[gStrLen]); progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
          END;
          INC(progLen)
        END
      END;

    ELSIF (Strings.Compare(t, "char") = 0) OR (Strings.Compare(t, "[char]") = 0) THEN
      IF tokIdx < tokCount THEN
        n := ORD(tokBuf[tokIdx][0]); INC(tokIdx);
        IF GetState() = 0 THEN Push(n)
        ELSE progIns[progLen].op := OP_LIT; progIns[progLen].ival := n; progIns[progLen].svalIdx := -1; INC(progLen) END
      END;

    ELSIF Strings.Compare(t, "postpone") = 0 THEN
      IF tokIdx < tokCount THEN
        Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
        idx := FindEntry(lw);
        IF idx < 0 THEN Error("postpone: unknown word"); RETURN END;
        IF entries[idx].isImmediate THEN
          progIns[progLen].op := OP_CALL; progIns[progLen].ival := 0;
          IF gStrLen < STR_POOL THEN
            Strings.Copy(lw, gStr[gStrLen]); progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
          END; INC(progLen)
        ELSE
          progIns[progLen].op := OP_LIT; progIns[progLen].ival := entries[idx].id; progIns[progLen].svalIdx := -1; INC(progLen);
          progIns[progLen].op := OP_CALL; progIns[progLen].ival := 0;
          IF gStrLen < STR_POOL THEN
            Strings.Copy("compile,", gStr[gStrLen]); progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
          END; INC(progLen)
        END
      END;

    ELSIF (Strings.Compare(t, "'") = 0) OR (Strings.Compare(t, "[']") = 0) THEN
      IF tokIdx < tokCount THEN
        Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
        idx := FindEntry(lw);
        IF idx < 0 THEN Error("': unknown word"); RETURN END;
        IF GetState() = 0 THEN Push(entries[idx].id)
        ELSE progIns[progLen].op := OP_LIT; progIns[progLen].ival := entries[idx].id; progIns[progLen].svalIdx := -1; INC(progLen) END
      END;

    ELSIF Strings.Compare(t, "see") = 0 THEN
      IF tokIdx < tokCount THEN
        Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
        idx := FindEntry(lw);
        IF idx < 0 THEN Out.String("Unknown: "); Out.String(lw); Out.Ln
        ELSE
          CASE entries[idx].kind OF
            EKPRIM: Out.String(lw); Out.String(" is a primitive"); Out.Ln
          | EKWORD:
              Out.String(": "); Out.String(lw); Out.Ln;
              SeeCode(entries[idx].code); Out.String(";"); Out.Ln
          | EKDEFINING:
              Out.String(": "); Out.String(lw); Out.Ln;
              SeeCode(entries[idx].code); Out.String("does>"); Out.Ln;
              SeeCode(entries[idx].doesCode); Out.String(";"); Out.Ln
          | EKCREATE:
              Out.String(lw); Out.String(" CREATE body="); Out.Int(entries[idx].bodyAddr, 0); Out.Ln
          ELSE
          END
        END
      END;

    ELSIF Strings.Compare(t, "help") = 0 THEN
      IF tokIdx < tokCount THEN
        Strings.Copy(tokBuf[tokIdx], s); INC(tokIdx);
        PrintHelp(s)
      ELSE
        Out.String("Usage: help <word>"); Out.Ln
      END;

    ELSIF GetState() = 0 THEN (* Interpret mode *)

      IF Strings.Compare(t, "marker") = 0 THEN
        IF tokIdx < tokCount THEN
          Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
          i := nMarkers;
          Strings.Copy(lw, mName[i]);
          mNEntries[i] := nEntries; mHeapSz[i] := heapTop;
          mGInsLen[i] := gInsLen; mGStrLen[i] := gStrLen;
          INC(nMarkers);
          progLen := 0; doesPos := -1;
          progIns[0].op := OP_EXECMARKER; progIns[0].ival := i; progIns[0].svalIdx := -1;
          progIns[1].op := OP_EXIT; progIns[1].ival := 0; progIns[1].svalIdx := -1;
          progLen := 2;
          CommitCode(code);
          e.kind := EKWORD; e.code := code; e.doesCode.insStart := 0; e.doesCode.insLen := 0;
          e.primFn := PfNoop; e.bodyAddr := 0; e.isImmediate := FALSE; e.id := 0;
          idx := RegisterEntry(lw, e)
        END;

      ELSIF Strings.Compare(t, "is") = 0 THEN
        n := Pop();
        IF tokIdx < tokCount THEN
          Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
          idx := FindEntry(lw);
          IF (idx < 0) OR (entries[idx].kind # EKCREATE) THEN Error("is: not a deferred word")
          ELSE HeapSet(entries[idx].bodyAddr, n) END
        END;

      ELSIF Strings.Compare(t, "include") = 0 THEN
        IF tokIdx < tokCount THEN
          Strings.Copy(tokBuf[tokIdx], s); INC(tokIdx);
          Strings.Copy(s, loadFileName); runLoadFile()
        END;

      ELSIF Strings.Compare(t, "create") = 0 THEN
        IF tokIdx < tokCount THEN
          Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
          e.kind := EKCREATE; e.bodyAddr := heapTop;
          e.code.insStart := 0; e.code.insLen := 0;
          e.doesCode.insStart := 0; e.doesCode.insLen := 0;
          e.primFn := PfNoop; e.isImmediate := FALSE; e.id := 0;
          idx := RegisterEntry(lw, e);
          Strings.Copy(lw, lastWord)
        END;

      ELSIF Strings.Compare(t, ":") = 0 THEN
        IF tokIdx < tokCount THEN
          Strings.Copy(tokBuf[tokIdx], current); Strings.ToLower(current); INC(tokIdx);
          Strings.Copy(current, lastWord);
          progLen := 0; doesPos := -1; nLocals := 0;
          cstackTop := 0; leaveTop := 0; leaveTotal := 0;
          SetState(1)
        END;

      ELSE
        (* Check for defining words *)
        idx := FindEntry(t);
        IF (idx >= 0) & (entries[idx].kind = EKDEFINING) THEN
          IF tokIdx < tokCount THEN
            Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
            e.kind := EKCREATE; e.bodyAddr := heapTop;
            e.code.insStart := 0; e.code.insLen := 0;
            e.doesCode := entries[idx].doesCode;
            e.primFn := PfNoop; e.isImmediate := FALSE; e.id := 0;
            j := RegisterEntry(lw, e);
            RunEntry(idx)
          END
        ELSIF idx >= 0 THEN
          RunEntry(idx)
        ELSIF TryParse(t, n) THEN
          Push(n)
        ELSE
          Error("Unknown word: "); Strings.Append(t, errMsg)
        END
      END

    ELSE (* Compile mode *)

      IF Strings.Compare(t, ";") = 0 THEN
        IF nLocals > 0 THEN
          progIns[progLen].op := OP_LOCALSEXIT; progIns[progLen].ival := 0;
          progIns[progLen].svalIdx := -1; INC(progLen)
        END;
        progIns[progLen].op := OP_EXIT; progIns[progLen].ival := 0;
        progIns[progLen].svalIdx := -1; INC(progLen);
        nLocals := 0;
        IF doesPos >= 0 THEN
          (* Split into code and doesCode *)
          e.kind := EKDEFINING;
          n := gInsLen;
          FOR i := 0 TO doesPos - 1 DO
            IF gInsLen < POOL_SIZE THEN gIns[gInsLen] := progIns[i]; INC(gInsLen) END
          END;
          e.code.insStart := n; e.code.insLen := doesPos;
          n := gInsLen;
          FOR i := doesPos TO progLen - 1 DO
            IF gInsLen < POOL_SIZE THEN gIns[gInsLen] := progIns[i]; INC(gInsLen) END
          END;
          e.doesCode.insStart := n; e.doesCode.insLen := progLen - doesPos;
          ResolveCalls(e.code); ResolveCalls(e.doesCode)
        ELSE
          e.kind := EKWORD;
          CommitCode(code); e.code := code;
          e.doesCode.insStart := 0; e.doesCode.insLen := 0;
          ResolveCalls(e.code)
        END;
        e.primFn := PfNoop; e.bodyAddr := 0; e.isImmediate := FALSE; e.id := 0;
        idx := RegisterEntry(current, e);
        SetState(0); doesPos := -1;

      ELSIF Strings.Compare(t, "does>") = 0 THEN
        doesPos := progLen;

      ELSIF Strings.Compare(t, "create") = 0 THEN
        (* create inside a defining word: do nothing at compile time *)

      ELSIF Strings.Compare(t, "{") = 0 THEN
        (* Local variables *)
        nLocals := 0;
        WHILE (tokIdx < tokCount) & (Strings.Compare(tokBuf[tokIdx], "}") # 0) DO
          IF Strings.Compare(tokBuf[tokIdx], "--") = 0 THEN
            WHILE (tokIdx < tokCount) & (Strings.Compare(tokBuf[tokIdx], "}") # 0) DO INC(tokIdx) END
          ELSE
            IF nLocals < MAX_LOCALS THEN
              Strings.Copy(tokBuf[tokIdx], localNames[nLocals]); Strings.ToLower(localNames[nLocals]);
              INC(nLocals)
            END;
            INC(tokIdx)
          END
        END;
        IF tokIdx < tokCount THEN INC(tokIdx) END; (* consume } *)
        progIns[progLen].op := OP_LOCALSENTER; progIns[progLen].ival := nLocals;
        progIns[progLen].svalIdx := -1; INC(progLen);
        FOR i := nLocals - 1 TO 0 BY -1 DO
          progIns[progLen].op := OP_LOCALSET; progIns[progLen].ival := i;
          IF gStrLen < STR_POOL THEN
            Strings.Copy(localNames[i], gStr[gStrLen]); progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
          ELSE progIns[progLen].svalIdx := -1 END;
          INC(progLen)
        END;

      ELSIF Strings.Compare(t, "->") = 0 THEN
        IF tokIdx < tokCount THEN
          Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
          i := 0; idx := -1;
          WHILE i < nLocals DO
            IF Strings.Compare(localNames[i], lw) = 0 THEN idx := i END; INC(i)
          END;
          IF idx < 0 THEN Error("Unknown local: "); Strings.Append(lw, errMsg); RETURN END;
          progIns[progLen].op := OP_LOCALSET; progIns[progLen].ival := idx;
          IF gStrLen < STR_POOL THEN
            Strings.Copy(lw, gStr[gStrLen]); progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
          ELSE progIns[progLen].svalIdx := -1 END;
          INC(progLen)
        END;

      ELSIF Strings.Compare(t, "is") = 0 THEN
        n := Pop();
        IF tokIdx < tokCount THEN
          Strings.Copy(tokBuf[tokIdx], lw); Strings.ToLower(lw); INC(tokIdx);
          idx := FindEntry(lw);
          IF (idx < 0) OR (entries[idx].kind # EKCREATE) THEN Error("is: not a deferred word")
          ELSE HeapSet(entries[idx].bodyAddr, n) END
        END

      ELSE
        (* Check if it's a local variable name *)
        i := 0; idx := -1;
        WHILE i < nLocals DO
          IF Strings.Compare(localNames[i], t) = 0 THEN idx := i END; INC(i)
        END;
        IF idx >= 0 THEN
          progIns[progLen].op := OP_LOCALGET; progIns[progLen].ival := idx;
          IF gStrLen < STR_POOL THEN
            Strings.Copy(t, gStr[gStrLen]); progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
          ELSE progIns[progLen].svalIdx := -1 END;
          INC(progLen)
        ELSIF TryParse(t, n) THEN
          progIns[progLen].op := OP_LIT; progIns[progLen].ival := n; progIns[progLen].svalIdx := -1; INC(progLen)
        ELSE
          (* Look up as a word *)
          idx := FindEntry(t);
          IF idx >= 0 THEN
            IF entries[idx].isImmediate THEN
              RunEntry(idx)
            ELSE
              progIns[progLen].op := OP_CALL; progIns[progLen].ival := 0;
              IF gStrLen < STR_POOL THEN
                Strings.Copy(t, gStr[gStrLen]); progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
              ELSE progIns[progLen].svalIdx := -1 END;
              INC(progLen)
            END
          ELSIF Strings.Compare(t, current) = 0 THEN
            (* recursion during compilation *)
            progIns[progLen].op := OP_CALL; progIns[progLen].ival := 0;
            IF gStrLen < STR_POOL THEN
              Strings.Copy(t, gStr[gStrLen]); progIns[progLen].svalIdx := gStrLen; INC(gStrLen)
            ELSE progIns[progLen].svalIdx := -1 END;
            INC(progLen)
          ELSE
            Error("Unknown word: "); Strings.Append(t, errMsg)
          END
        END
      END
    END (* compile mode *)
  END (* WHILE *)
END Process;

(* ── File loading ─────────────────────────────────────────────────── *)

PROCEDURE HasUnclosedString(s: ARRAY OF CHAR): BOOLEAN;
(* returns TRUE if s contains an s" or ." opened but not closed *)
VAR i, len, j: INTEGER; inStr: BOOLEAN; tok: ARRAY 256 OF CHAR;
    delim: CHAR;
BEGIN
  len := Strings.Length(s); inStr := FALSE; i := 0; delim := '"';
  WHILE i < len DO
    WHILE (i < len) & ((s[i] = ' ') OR (s[i] = 9X) OR (s[i] = 0AX)) DO INC(i) END;
    IF i < len THEN
      j := 0;
      WHILE (i < len) & (s[i] # ' ') & (s[i] # 9X) & (s[i] # 0AX) DO
        IF j < 255 THEN tok[j] := s[i]; INC(j) END;
        INC(i)
      END;
      tok[j] := 0X;
      IF ~inStr THEN
        IF (Strings.Compare(tok, 's"') = 0) OR (Strings.Compare(tok, '."') = 0) THEN
          inStr := TRUE; delim := '"'
        ELSIF Strings.Compare(tok, ".(") = 0 THEN
          inStr := TRUE; delim := ')'
        END
      ELSE
        IF (j > 0) & (tok[j-1] = delim) THEN inStr := FALSE END
      END
    END
  END;
  RETURN inStr
END HasUnclosedString;

PROCEDURE LoadFile(fn: ARRAY OF CHAR);
VAR f: Files.File; r: Files.Rider;
    line: ARRAY 4096 OF CHAR;
    cont: ARRAY 512 OF CHAR;
    i: INTEGER; c: BYTE; eofSeen: BOOLEAN;
    nl: ARRAY 4 OF CHAR;  (* " " + CHR(10) + " " + NUL — newline marker token *)
BEGIN
  f := Files.Old(fn);
  IF f = NIL THEN
    Out.String("Cannot open: "); Out.String(fn); Out.Ln; RETURN
  END;
  Files.Set(r, f, 0);
  nl[0] := ' '; nl[1] := 0AX; nl[2] := ' '; nl[3] := 0X;
  LOOP
    i := 0;
    LOOP
      Files.Read(r, c);
      IF r.eof OR (c = 10) THEN EXIT END;
      IF (c # 13) & (i < 509) THEN line[i] := CHR(c); INC(i) END
    END;
    line[i] := 0X;
    eofSeen := r.eof;
    Trim(line);
    (* Accumulate continuation lines when a string literal spans lines *)
    WHILE HasUnclosedString(line) & ~eofSeen DO
      i := 0;
      LOOP
        Files.Read(r, c);
        IF r.eof OR (c = 10) THEN EXIT END;
        IF (c # 13) & (i < 509) THEN cont[i] := CHR(c); INC(i) END
      END;
      cont[i] := 0X;
      eofSeen := r.eof;
      Trim(cont);
      Strings.Append(nl, line);
      Strings.Append(cont, line)
    END;
    IF (Strings.Length(line) > 0) &
       ~((Strings.Length(line) > 1) & (line[0] = '#') & (line[1] = '!')) THEN
      SplitStr(line);
      tokIdx := 0;
      Process;
      IF errFlag THEN
        Out.String("Error in file: "); Out.String(errMsg); Out.Ln;
        errFlag := FALSE;
        dsp := 0; rsp := 0; callDepth := 0
      END
    END;
    IF eofSeen THEN EXIT END
  END;
  Files.Close(f)
END LoadFile;

PROCEDURE DoLoadFile; BEGIN LoadFile(loadFileName) END DoLoadFile;

(* ── Late-bound primitives that need Process/LoadFile ─────────────── *)

PROCEDURE PfEvaluate;
VAR idx: INTEGER; s: ARRAY STR_LEN OF CHAR;
BEGIN
  idx := Pop();
  IF (idx >= 0) & (idx < strTabLen) THEN
    Strings.Copy(strTab[idx], s);
    SplitStr(s); tokIdx := 0;
    Process
  ELSE Error("evaluate: bad idx") END
END PfEvaluate;

PROCEDURE PfInclude;
VAR s: ARRAY STR_LEN OF CHAR;
BEGIN
  (* stack: str-idx *)
  s[0] := 0X;
  (* actually include is handled in Process; this is here for completeness *)
END PfInclude;

(* ── Init primitives ──────────────────────────────────────────────── *)

PROCEDURE InitPrims;

  PROCEDURE Prim(name: ARRAY OF CHAR; fn: PrimFn; imm: BOOLEAN);
  VAR e: Entry; idx: INTEGER;
  BEGIN
    e.kind := EKPRIM; e.primFn := fn; e.bodyAddr := 0;
    e.code.insStart := 0; e.code.insLen := 0;
    e.doesCode.insStart := 0; e.doesCode.insLen := 0;
    e.isImmediate := imm; e.id := 0;
    idx := RegisterEntry(name, e);
    IF imm THEN entries[idx].isImmediate := TRUE END
  END Prim;

BEGIN
  (* Hot ops: register as prims so execute works on them *)
  Prim("+",    PfPlus,    FALSE); Prim("-",   PfMinus,  FALSE);
  Prim("*",    PfMul,     FALSE); Prim("/",   PfDiv,    FALSE);
  Prim("mod",  PfMod,     FALSE); Prim("dup", PfDup2,   FALSE);
  Prim("drop", PfDrop2,   FALSE); Prim("swap",PfSwap2,  FALSE);
  Prim("over", PfOver2,   FALSE); Prim("rot", PfRot2,   FALSE);
  Prim("=",    PfEq2,     FALSE); Prim("<",   PfLt2,    FALSE);
  Prim(">",    PfGt2,     FALSE); Prim("0=",  PfZEq2,   FALSE);
  Prim(">r",   PfToR2,    FALSE); Prim("r>",  PfRFrom2, FALSE);
  Prim("r@",   PfRAt2,    FALSE); Prim("@",   PfFetch2, FALSE);
  Prim("!",    PfStore2,  FALSE); Prim("c@",  PfCFetch2,FALSE);
  Prim("c!",   PfCStore2, FALSE);
  Prim("and",     PfAnd2,        FALSE); Prim("or",    PfOr,         FALSE);
  Prim("xor",     PfXor,         FALSE); Prim("invert", PfInvert,    FALSE);
  Prim("lshift",  PfLshift,      FALSE); Prim("rshift", PfRshift,    FALSE);
  Prim("depth",   PfDepth,       FALSE); Prim("pick",  PfPick,       FALSE);
  Prim(".",       PfDot,         FALSE); Prim("emit",  PfEmit,       FALSE);
  Prim("cr",      PfCr,          FALSE); Prim("at-xy", PfAtXy,       FALSE);
  Prim(".s",      PfDots,        FALSE); Prim("type",  PfType,       FALSE);
  Prim("s=",      PfSEq,         FALSE); Prim("s+",   PfSPlus,       FALSE);
  Prim("s.clear", PfSClear,      FALSE); Prim("s.s",  PfSDs,         FALSE);
  Prim("accept",  PfAccept,      FALSE); Prim("key",   PfKey,        FALSE);
  Prim("base",    PfBase,        FALSE); Prim("hex",   PfHex,        FALSE);
  Prim("decimal", PfDec,         FALSE); Prim("octal", PfOct,        FALSE);
  Prim("binary",  PfBin,         FALSE); Prim("cell",  PfCellSz,     FALSE);
  Prim("cell+",   PfCellP,       FALSE); Prim("cells", PfCells,      FALSE);
  Prim(",",       PfComma,       FALSE); Prim("c,",   PfCComma,      FALSE);
  Prim("here",    PfHere,        FALSE); Prim("allot", PfAllot,      FALSE);
  Prim("fill",    PfFill,        FALSE); Prim("dump",  PfDump,       FALSE);
  Prim("erase",   PfErase,       FALSE); Prim("blank", PfBlank,      FALSE);
  Prim("state",   PfState,       FALSE); Prim("immediate", PfImm,    FALSE);
  Prim("execute", PfExecute,     FALSE); Prim("compile,", PfCompileComma, FALSE);
  Prim("bye",     PfBye,         FALSE); Prim("words", PfWords,      FALSE);
  Prim("help-set",PfHelpSet,    FALSE);
  Prim(">body",   PfToBody,      FALSE); Prim("body>", PfBodyFrom,   FALSE);
  Prim("/mod",    PfSlashMod,    FALSE); Prim("*/",   PfStarSlash,   FALSE);
  Prim("*/mod",   PfStarSlashMod,FALSE); Prim("roll", PfRoll,        FALSE);
  Prim("[",       PfLBracket,    TRUE ); Prim("]",    PfRBracket,    FALSE);
  Prim("literal", PfLiteral,     TRUE ); Prim("catch", PfCatch,      FALSE);
  Prim("throw",   PfThrow,       FALSE); Prim("noop",  PfNoop,       FALSE);
  Prim("2over",   Pf2Over,       FALSE); Prim("0<",   PfLt0,         FALSE);
  Prim("0>",      PfGt0,         FALSE); Prim("0<>",  PfNe0,         FALSE);
  Prim("<>",      PfNe,          FALSE); Prim("u<",   PfULt,         FALSE);
  Prim("u>",      PfUGt,         FALSE); Prim("char+", PfCharP,      FALSE);
  Prim("chars",   PfChars,       FALSE); Prim("count", PfCount,      FALSE);
  Prim("move",    PfMove,        FALSE); Prim("cmove", PfCMove,      FALSE);
  Prim("cmove>",  PfCMoveGt,     FALSE); Prim("s>d",  PfS2D,         FALSE);
  Prim("d>s",     PfD2S,         FALSE); Prim("um*",  PfUMStar,      FALSE);
  Prim("um/mod",  PfUMSlashMod,  FALSE); Prim("sm/rem", PfSMRem,     FALSE);
  Prim("evaluate",PfEvaluate,    FALSE); Prim("2>r",  Pf2Tor,        FALSE);
  Prim("2r>",     Pf2RFrom,      FALSE); Prim("2r@",  Pf2RAt,        FALSE);
  Prim("u.",      PfUDot,        FALSE); Prim(".r",   PfDotR,        FALSE);
  Prim("u.r",     PfUDotR,       FALSE); Prim("bl",   PfBl,          FALSE);
  Prim("space",   PfSpace,       FALSE); Prim("spaces", PfSpaces,    FALSE);
  Prim("pad",     PfPad,         FALSE); Prim("unused", PfUnused,    FALSE);
  Prim("compare", PfCompare,     FALSE); Prim("within", PfWithin,    FALSE);
  Prim("bounds",  PfBounds,      FALSE); Prim("abort",  PfAbort,     FALSE);
  Prim("quit",    PfQuit,        FALSE); Prim("?dup",   PfQDup,      FALSE);
  Prim("2nip",    Pf2Nip,        FALSE); Prim("<#",     PfPicStart,  FALSE);
  Prim("#",       PfPicDigit,    FALSE); Prim("#s",     PfPicDigits, FALSE);
  Prim("sign",    PfPicSign,     FALSE); Prim("hold",   PfHold,      FALSE);
  Prim("holds",   PfHolds,       FALSE); Prim("#>",     PfPicEnd,    FALSE);
  Prim("sp@",     PfSpAt,        FALSE); Prim("sp!",    PfSpStore,   FALSE);
  Prim("i",       PfI,           FALSE); Prim("j",      PfJ,         FALSE);
  Prim("unloop",  PfUnloop,      FALSE);
  Prim("if",      PfIf,          TRUE ); Prim("else",   PfElse,      TRUE );
  Prim("then",    PfThen,        TRUE ); Prim("begin",  PfBegin,     TRUE );
  Prim("until",   PfUntil,       TRUE ); Prim("again",  PfAgain,     TRUE );
  Prim("while",   PfWhile,       TRUE ); Prim("repeat", PfRepeat,    TRUE );
  Prim("do",      PfDo,          TRUE ); Prim("?do",    PfQDo,       TRUE );
  Prim("loop",    PfLoop,        TRUE ); Prim("+loop",  PfPLoop,     TRUE );
  Prim("leave",   PfLeave,       TRUE ); Prim("recurse",PfRecurse,   TRUE );
  Prim("exit",    PfExit,        TRUE );

  (* Set up heap layout *)
  padAddr := heapTop;
  INC(heapTop, 84)
END InitPrims;

(* ── REPL ─────────────────────────────────────────────────────────── *)

PROCEDURE Repl;
VAR line: ARRAY 256 OF CHAR; fn: ARRAY 256 OF CHAR; i: INTEGER;
    wrapLine: ARRAY 512 OF CHAR; needWrap: BOOLEAN; idx: INTEGER;
    emptyCount: INTEGER;
BEGIN
  InitPrims;
  replDone := FALSE;

  (* Load stdlib from exe directory *)
  ExePath("stdlib.fs", fn);
  LoadFile(fn);

  (* Load file from command line if given *)
  IF Args.Count() > 0 THEN
    Args.Get(1, fn); LoadFile(fn)
  END;

  Out.String("BadgerForth 1.0 (Oberon)"); Out.Ln;

  emptyCount := 0;
  LOOP
    IF replDone THEN EXIT END;
    errFlag := FALSE;
    History.ReadLine("> ", line);
    Trim(line);
    IF Strings.Length(line) = 0 THEN
      INC(emptyCount); IF emptyCount >= 3 THEN EXIT END
    ELSE
      emptyCount := 0;
      History.Add(line);
      (* Determine whether to wrap in anonymous word *)
      SplitStr(line); tokIdx := 0;
      needWrap := TRUE;
      IF tokCount > 0 THEN
        Strings.Copy(tokBuf[0], wrapLine); Strings.ToLower(wrapLine);
        IF (Strings.Compare(wrapLine, ":") = 0) OR
           (Strings.Compare(wrapLine, "include") = 0) OR
           (Strings.Compare(wrapLine, "bye") = 0) OR
           (Strings.Compare(wrapLine, "help") = 0) OR
           (Strings.Compare(wrapLine, "see") = 0) OR
           (Strings.Compare(wrapLine, "marker") = 0) THEN
          needWrap := FALSE
        ELSE
          idx := FindEntry(wrapLine);
          IF (idx >= 0) & (entries[idx].kind = EKDEFINING) THEN needWrap := FALSE END
        END;
        IF needWrap THEN
          i := 0;
          WHILE i < tokCount DO
            Strings.Copy(tokBuf[i], wrapLine); Strings.ToLower(wrapLine);
            IF (Strings.Compare(wrapLine, "create") = 0) OR
               (Strings.Compare(wrapLine, ":") = 0) THEN
              needWrap := FALSE
            ELSE
              idx := FindEntry(wrapLine);
              IF (idx >= 0) & (entries[idx].kind = EKDEFINING) THEN needWrap := FALSE END
            END;
            INC(i)
          END
        END
      END;
      IF needWrap THEN
        Strings.Copy(": __anon__ ", wrapLine);
        Strings.Append(line, wrapLine); Strings.Append(" ; __anon__", wrapLine);
        SplitStr(wrapLine); tokIdx := 0
      END;
      Process;
      IF errFlag THEN
        Out.String("Error: "); Out.String(errMsg); Out.Ln;
        dsp := 0; rsp := 0; callDepth := 0; lframesTop := 0;
        cstackTop := 0; leaveTop := 0; leaveTotal := 0;
        SetState(0); doesPos := -1; nLocals := 0;
        progLen := 0; errFlag := FALSE
      ELSE
        Out.String(" ok"); Out.Ln
      END;
      (* Remove anonymous word - it's always the last entry if present *)
      IF (nEntries > 0) & (Strings.Compare(entries[nEntries-1].name, "__anon__") = 0) THEN
        DEC(nEntries)
      END
    END
  END
END Repl;

BEGIN
  (* Determine exe directory from argv[0] *)
  InitExeDir;

  (* Initialize state *)
  dsp := 0; rsp := 0; callDepth := 0;
  gInsLen := 0; gStrLen := 0; strTabLen := 0;
  nEntries := 0; nextId := 0; nMarkers := 0;
  progLen := 0; compiling := FALSE; doesPos := -1;
  cstackTop := 0; leaveTop := 0; leaveTotal := 0;
  nLocals := 0; lframesTop := 0;
  picLen := 0; picBuf[0] := 0X;
  errFlag := FALSE; errMsg[0] := 0X; replDone := FALSE;
  helpCount := 0;

  (* Heap init: base=10, state=0 *)
  heapTop := 0;
  baseAddr  := 0;  HeapSet(baseAddr,  10);
  stateAddr := CELL; HeapSet(stateAddr, 0);
  heapTop   := 2 * CELL;
  padAddr := 0; (* set by InitPrims *)

  runLoadFile := DoLoadFile;
  Repl
END Forth.
