package main

import (
	"fmt"
	"math"
	"os"
	"strconv"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"
)

type u8 uint8
type u32 uint32
type u64 uint64
type Lnk u64

const (
	U64_PER_KB u64 = 0x80
	U64_PER_MB u64 = 0x20000
	U64_PER_GB u64 = 0x8000000

	HEAP_SIZE        u64 = 8 * U64_PER_GB * u64(unsafe.Sizeof(u64(0)))
	MEM_SPACE        u64 = HEAP_SIZE / MAX_WORKERS / u64(unsafe.Sizeof(u64(0)))
	NORMAL_SEEN_MCAP u64 = HEAP_SIZE / u64(unsafe.Sizeof(u64(0))) / (u64(unsafe.Sizeof(u64(0))) * 8)
)

// stubs for testing
const (
	GENERATED_NUM_THREADS_CONTENT = 8
	MAX_ARITY                     = 16
	MAX_WORKERS                   = 8
)

// constants
const (
	// MAX_WORKERS u64 = GENERATED_NUM_THREADS_CONTENT
	MAX_DYNFUNS       u64 = 65536
	stk_growth_factor     = 16
)

const (
	VAL u64 = 1
	EXT u64 = 0x100000000
	ARI u64 = 0x100000000000000
	TAG u64 = 0x1000000000000000

	DP0 u64 = 0x0 // points to the dup node that binds this variable (left side)
	DP1 u64 = 0x1 // points to the dup node that binds this variable (right side)
	VAR u64 = 0x2 // points to the λ that binds this variable
	ARG u64 = 0x3 // points to the occurrence of a bound variable a linear argument
	ERA u64 = 0x4 // signals that a binder doesn't use its bound variable
	LAM u64 = 0x5 // arity = 2
	APP u64 = 0x6 // arity = 2
	PAR u64 = 0x7 // arity = 2 // TODO: rename to SUP
	CTR u64 = 0x8 // arity = user defined
	CAL u64 = 0x9 // arity = user defined
	OP2 u64 = 0xA // arity = 2
	U32 u64 = 0xB // arity = 0 (unboxed)
	F32 u64 = 0xC // arity = 0 (unboxed)
	NIL u64 = 0xF // not used

	ADD u64 = 0x0
	SUB u64 = 0x1
	MUL u64 = 0x2
	DIV u64 = 0x3
	MOD u64 = 0x4
	AND u64 = 0x5
	OR  u64 = 0x6
	XOR u64 = 0x7
	SHL u64 = 0x8
	SHR u64 = 0x9
	LTN u64 = 0xA
	LTE u64 = 0xB
	EQL u64 = 0xC
	GTE u64 = 0xD
	GTN u64 = 0xE
	NEQ u64 = 0xF
)

//GENERATED_CONSTRUCTOR_IDS_START//
/* GENERATED_CONSTRUCTOR_IDS_CONTENT */
//GENERATED_CONSTRUCTOR_IDS_END//

type Arr []u64
type Stk []u64

type Worker struct {
	tid               u64
	cost              u64
	has_work          u64
	has_work_mutex    sync.Mutex
	has_work_signal   sync.Cond
	has_result        u64
	has_result_mutex  sync.Mutex
	has_result_signal sync.Cond
	free              [MAX_ARITY]Stk
	node              []Lnk
}

var (
	workers [MAX_WORKERS]Worker
)

func array_write(arr Arr, idx, value u64) {
	arr = append(arr, value)
}
func array_read(arr Arr, idx u64) u64 {
	return arr[idx]
}

func stk_init(stack Stk) {
	stack = make(Stk, stk_growth_factor)
	return
}

// func stk_push(stack Stk, value u64) {
// 	stack = append(stack, value)
// 	return
// }
func stk_pop(stack Stk) u64 {
	if len(stack) == 0 {
		return u64(math.MaxUint64)
	}
	value := stack[len(stack)-1]
	stack = stack[:len(stack)-1]
	return value
}

func stk_find(stack Stk, val u64) u64 {
	for i := range stack {
		if stack[i] == val {
			return u64(i)
		}
	}
	return u64(math.MaxUint64)
}

func Var(pos u64) Lnk {
	return Lnk((VAR * TAG) | pos)
}

func Dp0(col, pos u64) Lnk {
	return Lnk((DP0 * TAG) | (col * EXT) | pos)
}

func Dp1(col, pos u64) Lnk {
	return Lnk((DP1 * TAG) | (col * EXT) | pos)
}

func Arg(pos u64) Lnk {
	return Lnk((ARG * TAG) | pos)
}

func Era() Lnk {
	return Lnk(ERA * TAG)
}

func Lam(pos u64) Lnk {
	return Lnk((LAM * TAG) | pos)
}

func App(pos u64) Lnk {
	return Lnk((APP * TAG) | pos)
}

func Par(col, pos u64) Lnk {
	return Lnk((PAR * TAG) | (col * EXT) | pos)
}

func Op2(ope, pos u64) Lnk {
	return Lnk((OP2 * TAG) | (ope * EXT) | pos)
}

func U_32(val u64) Lnk {
	return Lnk((U32 * TAG) | val)
}

func Nil() Lnk {
	return Lnk(NIL * TAG)
}

func Ctr(ari, fun, pos u64) Lnk {
	return Lnk((CTR * TAG) | (ari * ARI) | (fun * EXT) | pos)
}

func Cal(ari, fun, pos u64) Lnk {
	return Lnk((CAL * TAG) | (ari * ARI) | (fun * EXT) | pos)
}

func get_tag(lnk Lnk) u64 {
	return u64(lnk) / TAG
}

func get_ext(lnk Lnk) u64 {
	return u64(lnk) / EXT & 0xFFFFFF
}

func get_val(lnk Lnk) u64 {
	return u64(lnk) & 0xFFFFFF
}

func get_ari(lnk Lnk) u64 {
	return u64(lnk) / ARI & 0xFFFFFF
}

func get_loc(lnk Lnk, arg u64) u64 {
	return get_val(lnk) + arg
}

func ask_lnk(mem *Worker, loc u64) Lnk {
	return mem.node[loc]
}

func ask_arg(mem *Worker, term Lnk, arg u64) u64 {
	return u64(ask_lnk(mem, get_loc(term, arg)))
}

func link(mem *Worker, loc u64, lnk Lnk) u64 {
	mem.node[loc] = lnk
	if get_tag(lnk) <= VAR {
		if get_tag(lnk) == DP1 {
			mem.node[get_loc(lnk, 1)] = Arg(loc)
		} else {
			mem.node[get_loc(lnk, 0)] = Arg(loc)

		}
	}
	return u64(lnk)
}

func alloc(mem *Worker, size u64) u64 {
	if size == 0 {
		return 0
	}
	reuse := stk_pop(mem.free[size])
	if reuse != u64(math.MaxUint64) {
		return reuse
	}
	loc := u64(len(mem.free))
	return mem.tid*MEM_SPACE + loc
}

func clear(mem *Worker, loc u64, size u64) {
	mem.free[size] = append(mem.free[size], loc)
}

func collect(mem *Worker, term Lnk) {
	switch get_tag(term) {
	case DP0:
		link(mem, get_loc(term, 0), Era())
	case DP1:
		link(mem, get_loc(term, 1), Era())
	case VAR:
		link(mem, get_loc(term, 0), Era())
	case LAM:
		if get_tag(Lnk(ask_arg(mem, term, 0))) != ERA {
			link(mem, get_loc(Lnk(ask_arg(mem, term, 0)), 0), Era())
		}
		collect(mem, Lnk(ask_arg(mem, term, 1)))
		clear(mem, get_loc(term, 0), 2)
	case APP:
		collect(mem, Lnk(ask_arg(mem, term, 0)))
		collect(mem, Lnk(ask_arg(mem, term, 1)))
		clear(mem, get_loc(term, 0), 2)
	case PAR:
		collect(mem, Lnk(ask_arg(mem, term, 0)))
		collect(mem, Lnk(ask_arg(mem, term, 1)))
		clear(mem, get_loc(term, 0), 1)
	case OP2:
		collect(mem, Lnk(ask_arg(mem, term, 0)))
		collect(mem, Lnk(ask_arg(mem, term, 1)))
	case U32:
		break
	case CTR:
	case CAL:
		arity := get_ari(term)
		for i := u64(0); i < arity; i++ {
			collect(mem, Lnk(ask_arg(mem, term, i)))
		}
		clear(mem, get_loc(term, 0), arity)
	}
}

func inc_cost(mem *Worker) {
	mem.cost++
}

func subst(mem *Worker, lnk, val Lnk) {
	if get_tag(lnk) != ERA {
		link(mem, get_loc(lnk, 0), val)
	} else {
		collect(mem, val)
	}
}

func cal_par(mem *Worker, host u64, term, argn Lnk, n u64) Lnk {
	inc_cost(mem)
	var (
		arity u64 = get_ari(term)
		fun   u64 = get_ext(term)
		fun0      = get_loc(term, 0)
		fun1      = get_loc(term, 1)
		par0      = get_loc(argn, 0)
	)
	for i := u64(0); i < arity; i++ {
		if i != n {
			var (
				leti u64 = alloc(mem, 3)
				argi u64 = ask_arg(mem, term, i)
			)
			link(mem, fun0+i, Dp0(get_ext(argn), leti))
			link(mem, fun1+i, Dp1(get_ext(argn), leti+1))
			link(mem, leti+2, Lnk(argi))
		} else {
			link(mem, fun0+i, Lnk(ask_arg(mem, argn, 0)))
			link(mem, fun1+i, Lnk(ask_arg(mem, argn, 1)))
		}
	}
	link(mem, par0+0, Cal(arity, fun, fun0))
	link(mem, par0+1, Cal(arity, fun, fun1))
	done := Par(get_ext(argn), par0)
	link(mem, host, done)
	return done
}

func reduce(mem *Worker, root, slen u64) Lnk {
	stack := Stk{}
	stk_init(stack)

	var (
		init u64 = 1
		host u32 = u32(root)
	)

	for {
		term := ask_lnk(mem, u64(host))

		if init == 1 {
			switch get_tag(term) {
			case APP:
				stack = append(stack, u64(host))
				init = 1
				host = u32(get_loc(term, 0))
				continue
			case DP0:
			case DP1:
				flag := atomic.Value{}
				flag.Store((mem.node[get_loc(term, 0)] + 6))
				flag1 := atomic.Value{}
				flag1.Store((mem.node[get_loc(term, 0)]))
				if !flag.CompareAndSwap(flag, flag1) {
					continue
				}
				stack = append(stack, u64(host))
				host = u32(get_loc(term, 2))
				continue
			case OP2:
				if slen == 1 || len(stack) > 0 {
					stack = append(stack, u64(host))
					stack = append(stack, get_loc(term, 0)|0x80000000)
					host = u32(get_loc(term, 1))
					continue
				}
			case CAL:
				fun := get_ext(term)
				ari := get_ari(term)
				_ = ari
				switch fun {
				//GENERATED_REWRITE_RULES_STEP_0_START//
				/* GENERATED_REWRITE_RULES_STEP_0_CONTENT */
				//GENERATED_REWRITE_RULES_STEP_0_END//
				}
			}
		} else {
			switch get_tag(term) {
			case APP:
				arg0 := ask_arg(mem, term, 0)
				switch get_tag(Lnk(arg0)) {
				case LAM:
					inc_cost(mem)
					subst(mem, Lnk(ask_arg(mem, Lnk(arg0), 0)), Lnk(ask_arg(mem, term, 1)))
					done := link(mem, u64(host), Lnk(ask_arg(mem, Lnk(arg0), 1)))
					_ = done
					clear(mem, get_loc(term, 0), 2)
					clear(mem, get_loc(Lnk(arg0), 0), 2)
					init = 1
					continue
				case PAR:
					inc_cost(mem)
					app0 := get_loc(term, 0)
					app1 := get_loc(term, 1)
					let0 := alloc(mem, 3)
					par0 := alloc(mem, 2)
					link(mem, let0+2, Lnk(ask_arg(mem, term, 1)))
					link(mem, app0+1, Dp0(get_ext(Lnk(arg0)), let0))
					link(mem, app0+0, Lnk(ask_arg(mem, Lnk(arg0), 0)))
					link(mem, app1+0, Lnk(ask_arg(mem, Lnk(arg0), 1)))
					link(mem, app1+1, Dp1(get_ext(Lnk(arg0)), let0+1))
					link(mem, par0+0, App(app0))
					link(mem, par0+1, App(app1))
					done := Par(get_ext(Lnk(arg0)), par0)
					link(mem, u64(host), done)
				} //switch arg0
			case DP0:
			case DP1:
				arg0 := ask_arg(mem, term, 2)
				switch get_tag(Lnk(arg0)) {
				case LAM:
					inc_cost(mem)
					let0 := get_loc(term, 0)
					par0 := get_loc(Lnk(arg0), 0)
					lam0 := alloc(mem, 2)
					lam1 := alloc(mem, 2)
					link(mem, let0+2, Lnk(ask_arg(mem, Lnk(arg0), 1)))
					link(mem, par0+1, Var(lam1))
					arg0_arg_0 := ask_arg(mem, Lnk(arg0), 0)
					link(mem, par0+0, Var(lam0))
					subst(mem, Lnk(arg0_arg_0), Par(get_ext(term), par0))
					term_arg_0 := ask_arg(mem, term, 0)
					link(mem, lam0+1, Dp0(get_ext(term), let0))
					subst(mem, Lnk(term_arg_0), Lam(lam0))
					term_arg_1 := ask_arg(mem, term, 1)
					link(mem, lam1+1, Dp1(get_ext(term), let0))
					subst(mem, Lnk(term_arg_1), Lam(lam1))
					if get_tag(term) == DP0 {
						done := Lam(lam0)
						link(mem, u64(host), done)
					} else {
						done := Lam(lam1)
						link(mem, u64(host), done)
					}
					init = 1
					continue
				case PAR:
					if get_ext(term) == get_ext(Lnk(arg0)) {
						inc_cost(mem)
						subst(mem, Lnk(ask_arg(mem, term, 0)), Lnk(ask_arg(mem, Lnk(arg0), 0)))
						subst(mem, Lnk(ask_arg(mem, term, 1)), Lnk(ask_arg(mem, Lnk(arg0), 1)))
						done := u64(0)
						_ = done
						if get_tag(term) == DP0 {
							done = link(mem, u64(host), Lnk(ask_arg(mem, Lnk(arg0), 0)))
						} else {
							done = link(mem, u64(host), Lnk(ask_arg(mem, Lnk(arg0), 0)))
						}
						clear(mem, get_loc(term, 0), 3)
						clear(mem, get_loc(Lnk(arg0), 0), 2)
						init = 1
						continue
					} else {
						inc_cost(mem)
						par0 := alloc(mem, 2)
						let0 := get_loc(term, 0)
						par1 := get_loc(Lnk(arg0), 0)
						let1 := alloc(mem, 3)
						link(mem, let0+2, Lnk(ask_arg(mem, Lnk(arg0), 0)))
						link(mem, let0+2, Lnk(ask_arg(mem, Lnk(arg0), 1)))
						term_arg_0 := ask_arg(mem, term, 0)
						term_arg_1 := ask_arg(mem, term, 1)
						link(mem, par0+0, Dp1(get_ext(term), let0))
						link(mem, par0+1, Dp1(get_ext(term), let1))
						link(mem, par0+0, Dp0(get_ext(term), let0))
						link(mem, par0+1, Dp0(get_ext(term), let1))
						subst(mem, Lnk(term_arg_0), Par(get_ext(Lnk(arg0)), par0))
						subst(mem, Lnk(term_arg_1), Par(get_ext(Lnk(arg0)), par1))
						done := Lnk(0)
						if get_tag(term) == DP0 {
							done = Par(u64(get_ext(term)), par0)
						} else {
							done = Par(u64(get_ext(term)), par1)
						}
						link(mem, u64(host), done)
					}
				case U32:
					inc_cost(mem)
					subst(mem, Lnk(ask_arg(mem, term, 0)), Lnk(arg0))
					subst(mem, Lnk(ask_arg(mem, term, 1)), Lnk(arg0))
					// done := u64(arg0) //wut
					link(mem, u64(host), Lnk(arg0))

				case CTR:
					inc_cost(mem)
					fun := get_ext(Lnk(arg0))
					arit := get_ari(Lnk(arg0))
					if arit == 0 {
						subst(mem, Lnk(ask_arg(mem, term, 0)), Ctr(0, fun, 0))
						subst(mem, Lnk(ask_arg(mem, term, 1)), Ctr(0, fun, 0))
						clear(mem, get_loc(term, 0), 3)
						done := link(mem, u64(host), Ctr(0, fun, 0))
						_ = done
					} else {
						ctr0 := get_loc(Lnk(arg0), 0)
						ctr1 := alloc(mem, arit)
						for i := u64(0); i < arit; i++ {
							leti := alloc(mem, 3)
							link(mem, ctr0+i, Dp0(get_ext(term), leti))
							link(mem, ctr1+i, Dp1(get_ext(term), leti))
						}
						leti := get_loc(term, 0)
						link(mem, leti+2, Lnk(ask_arg(mem, Lnk(arg0), arit-1)))
						term_arg_0 := ask_arg(mem, term, 0)
						link(mem, ctr0+arit-1, Dp0(get_ext(term), leti))
						subst(mem, Lnk(term_arg_0), Ctr(arit, fun, ctr0))
						term_arg_1 := ask_arg(mem, term, 1)
						link(mem, ctr0+arit-1, Dp1(get_ext(term), leti))
						subst(mem, Lnk(term_arg_1), Ctr(arit, fun, ctr1))
						done := Lnk(0)
						if get_tag(term) == DP0 {
							done = Ctr(arit, fun, ctr0)
						} else {
							done = Ctr(arit, fun, ctr1)
						}
						link(mem, u64(host), done)
					}

				} //switch arg0
				// flag := atomic.Value{}
				// flag.Store((mem.node[get_loc(term, 0)] + 6))
			case OP2:
				arg0 := ask_arg(mem, term, 0)
				arg1 := ask_arg(mem, term, 1)

				if get_tag(Lnk(arg0)) == U32 && get_tag(Lnk(arg1)) == U32 {
					inc_cost(mem)
					a := get_val(Lnk(arg0))
					b := get_val(Lnk(arg1))
					c := u64(0)
					switch get_ext(term) {
					case ADD:
						c = (a + b) & 0xFFFFFFFF
					case SUB:
						c = (a - b) & 0xFFFFFFFF
					case MUL:
						c = (a * b) & 0xFFFFFFFF
					case DIV:
						c = (a / b) & 0xFFFFFFFF
					case MOD:
						c = (a % b) & 0xFFFFFFFF
					case AND:
						c = (a & b) & 0xFFFFFFFF
					case OR:
						c = (a | b) & 0xFFFFFFFF
					case XOR:
						c = (a ^ b) & 0xFFFFFFFF
					case SHL:
						c = (a << b) & 0xFFFFFFFF
					case SHR:
						c = (a >> b) & 0xFFFFFFFF
					case LTN:
						if a < b {
							c = 1
						}
					case LTE:
						if a <= b {
							c = 1
						}
					case EQL:
						if a == b {
							c = 1
						}
					case GTE:
						if a >= b {
							c = 1
						}
					case GTN:
						if a > b {
							c = 1
						}
					case NEQ:
						if a != b {
							c = 1
						}
					}
					done := U_32(c)
					clear(mem, get_loc(term, 0), 2)
					link(mem, u64(host), done)
				} else if get_tag(Lnk(arg0)) == PAR {
					inc_cost(mem)
					op20 := get_loc(term, 0)
					op21 := get_loc(Lnk(arg0), 0)
					let0 := alloc(mem, 3)
					par0 := alloc(mem, 2)
					link(mem, let0+2, Lnk(arg1))
					link(mem, op20+1, Dp0(get_ext(Lnk(arg0)), let0))
					link(mem, op20+0, Lnk(ask_arg(mem, Lnk(arg0), 0)))
					link(mem, op20+0, Lnk(ask_arg(mem, Lnk(arg0), 1)))
					link(mem, op21+1, Dp1(get_ext(Lnk(arg0)), let0))
					link(mem, par0+0, Op2(get_ext(Lnk(arg0)), op20))
					link(mem, par0+1, Op2(get_ext(Lnk(arg0)), op21))
					done := Par(get_ext(Lnk(arg0)), par0)
					link(mem, u64(host), done)
				} else if get_tag(Lnk(arg1)) == PAR {
					inc_cost(mem)
					op20 := get_loc(term, 0)
					op21 := get_loc(Lnk(arg1), 0)
					let0 := alloc(mem, 3)
					par0 := alloc(mem, 2)
					link(mem, let0+2, Lnk(arg0))
					link(mem, op20+0, Dp0(get_ext(Lnk(arg1)), let0))
					link(mem, op20+1, Lnk(ask_arg(mem, Lnk(arg1), 0)))
					link(mem, op21+1, Lnk(ask_arg(mem, Lnk(arg1), 1)))
					link(mem, par0+0, Op2(get_ext(Lnk(arg1)), op20))
					link(mem, par0+1, Op2(get_ext(Lnk(arg1)), op21))
					done := Par(get_ext(Lnk(arg1)), par0)
					link(mem, u64(host), done)
				}
			case CAL:
				fun := get_ext(term)
				ari := get_ari(term)
				_ = ari
				switch fun {
				//GENERATED_REWRITE_RULES_STEP_1_START//
				/* GENERATED_REWRITE_RULES_STEP_1_CONTENT */
				//GENERATED_REWRITE_RULES_STEP_1_END//
				}
			} //switch term

		}
		item := stk_pop(stack)
		if item == u64(math.MaxUint64) {
			break
		} else {
			item = item >> 31
			host = u32(item & 0x7FFFFFFF)
		}
	}
	return ask_lnk(mem, root)
}

func set_bit(bits []u64, bit u64) {
	bits[bit>>6] |= 1 << (bit & 0x3F)
}

func get_bit(bits []u64, bit u64) u8 {
	return u8(bits[bit>>6] >> (1 << (bit & 0x3F)) & 1)
}

func normal_init() {
	for i := 0; i < len(normal_seen_data); i++ {
		normal_seen_data[i] = 0
	}
}

func normal(mem *Worker, host, sidx, slen u64) Lnk {
	normal_init()
	normal_go(mem, host, sidx, slen)
	normal_init()
	return normal_go(mem, host, 0, 1)
}

func normal_fork(tid, host, sidx, slen u64) {
	// todo
	workers[tid].has_work_mutex.Lock()
	workers[tid].has_work = (sidx << 48) | (slen << 32) | host
	workers[tid].has_work_signal.Broadcast()
	workers[tid].has_work_mutex.Unlock()
}
func normal_join(tid u64) u64 {
	// todo
	for {
		workers[tid].has_result_mutex.Lock()
		for workers[tid].has_result == math.MaxUint64 {
			workers[tid].has_result_signal.Wait()
		}
		done := workers[tid].has_result
		workers[tid].has_result = math.MaxUint64
		workers[tid].has_result_mutex.Unlock()
		return done
	}
}

var (
	ffi_cost u64
	ffi_size u64
	WG       sync.WaitGroup
)

func worker_stop(tid u64) {
	workers[tid].has_work_mutex.Lock()
	workers[tid].has_work = math.MaxUint64 - 1
	workers[tid].has_work_signal.Broadcast()
	workers[tid].has_work_mutex.Unlock()
}

func worker(tid u64) {
	for {
		workers[tid].has_work_mutex.Lock()
		for workers[tid].has_work == math.MaxUint64 {
			workers[tid].has_work_signal.Wait()
		}
		work := workers[tid].has_work
		if work == math.MaxUint64-1 {
			break
		}
		sidx := (work >> 48) & 0xFFFF
		slen := (work >> 32) & 0xFFFF
		host := (work >> 0) & 0xFFFFFFFF
		workers[tid].has_result = u64(normal_go(&workers[tid], host, sidx, slen))
		workers[tid].has_work = math.MaxUint64
		workers[tid].has_work_signal.Signal()
		workers[tid].has_work_mutex.Unlock()
	}
	WG.Done()
}

func ffi_normal(mem_data []Lnk, host u32) {
	for t := u64(0); t < MAX_WORKERS; t++ {
		workers[t].tid = t
		workers[t].node = mem_data
		for a := u64(0); a < MAX_ARITY; a++ {
			stk_init(workers[t].free[a])
		}
		workers[t].has_work = math.MaxUint64
		workers[t].has_work_mutex = sync.Mutex{}
		workers[t].has_work_signal = sync.Cond{}
		workers[t].has_result = math.MaxUint64
		workers[t].has_result_mutex = sync.Mutex{}
		workers[t].has_result_signal = sync.Cond{}
		WG.Add(1)
		go worker(t)
	}
	normal(&workers[0], u64(host), 0, MAX_WORKERS)
	ffi_cost = 0
	ffi_size = 0
	for i := u64(0); i < MAX_WORKERS; i++ {
		ffi_cost += workers[i].cost
		ffi_size += u64(len(workers[i].node))
	}
	for t := u64(0); t < MAX_WORKERS; t++ {
		worker_stop(t)
	}
	WG.Wait()
	for t := u64(0); t < MAX_WORKERS; t++ {
		for a := u64(0); a < MAX_ARITY; a++ {
			workers[t].free[a] = nil
		}
		workers[t].node = nil
	}
}

var normal_seen_data []u64 = make([]u64, NORMAL_SEEN_MCAP)

func normal_go(mem *Worker, host, sidx, slen u64) Lnk {
	term := ask_lnk(mem, host)
	if get_bit(normal_seen_data, host) != 0 {
		return term
	}
	term = reduce(mem, host, slen)
	set_bit(normal_seen_data, host)
	rec_size := u64(0)
	rec_locs := [16]u64{}
	switch get_tag(term) {
	case LAM:
		rec_locs[rec_size] = get_loc(term, 1)
		rec_size++
	case APP:
		rec_locs[rec_size] = get_loc(term, 0)
		rec_size++
		rec_locs[rec_size] = get_loc(term, 1)
		rec_size++
	case PAR:
		rec_locs[rec_size] = get_loc(term, 0)
		rec_size++
		rec_locs[rec_size] = get_loc(term, 1)
		rec_size++
	case DP0:
		rec_locs[rec_size] = get_loc(term, 2)
		rec_size++
	case DP1:
		rec_locs[rec_size] = get_loc(term, 2)
		rec_size++
	case OP2:
		if slen > 1 {
			rec_locs[rec_size] = get_loc(term, 1)
			rec_size++
		}
	case CTR:
	case CAL:
		ari := get_ari(term)
		for i := u64(0); i < ari; i++ {
			rec_locs[rec_size] = get_loc(term, i)
			rec_size++
		}
	}

	if rec_size > 2 && slen >= rec_size {
		space := slen / rec_size
		for i := u64(0); i < rec_size; i++ {
			normal_fork(sidx+i*space, rec_locs[i], sidx+i*space, space)
		}
		link(mem, rec_locs[0], normal_go(mem, rec_locs[0], sidx, space))
		for i := u64(1); i < rec_size; i++ {
			link(mem, get_loc(term, i), Lnk(normal_join(sidx+i*space)))
		}
	} else {
		for i := u64(0); i < rec_size; i++ {
			link(mem, rec_locs[i], normal_go(mem, rec_locs[i], sidx, slen))
		}
	}

	return term
}

func readback_vars(vars Stk, mem *Worker, term Lnk, seen Stk) {
	if stk_find(seen, u64(term)) != math.MaxUint64 {
		return
	}
	seen = append(seen, u64(term))
	switch get_tag(term) {
	case LAM:
		argm := ask_arg(mem, term, 0)
		body := ask_arg(mem, term, 1)
		if get_tag(Lnk(argm)) != ERA {
			vars = append(vars, u64(Var(get_loc(term, 0))))
		}
		readback_vars(vars, mem, Lnk(body), seen)
	case APP:
		lam := ask_arg(mem, term, 0)
		arg := ask_arg(mem, term, 1)
		readback_vars(vars, mem, Lnk(lam), seen)
		readback_vars(vars, mem, Lnk(arg), seen)
	case PAR:
		arg0 := ask_arg(mem, term, 0)
		arg1 := ask_arg(mem, term, 1)
		readback_vars(vars, mem, Lnk(arg0), seen)
		readback_vars(vars, mem, Lnk(arg1), seen)
	case DP0:
		arg := ask_arg(mem, term, 2)
		readback_vars(vars, mem, Lnk(arg), seen)
	case DP1:
		arg := ask_arg(mem, term, 2)
		readback_vars(vars, mem, Lnk(arg), seen)
	case OP2:
		arg0 := ask_arg(mem, term, 0)
		arg1 := ask_arg(mem, term, 1)
		readback_vars(vars, mem, Lnk(arg0), seen)
		readback_vars(vars, mem, Lnk(arg1), seen)
	case CTR:
	case CAL:
		arity := get_ari(term)
		for i := u64(0); i < arity; i++ {
			readback_vars(vars, mem, Lnk(ask_arg(mem, term, i)), seen)
		}
	}
}

func readback_decimal_go(chrs Stk, n u64) {
	if n > 0 {
		readback_decimal_go(chrs, n/10)
		chrs = append(chrs, '0'+n%10)
	}
}

func readback_decimal(chrs Stk, n u64) {
	if n == 0 {
		chrs = append(chrs, 0)
	} else {
		readback_decimal_go(chrs, n)
	}
}

func readback_term(chrs Stk, mem *Worker, term Lnk, vars Stk, dirs []Stk, id_to_name_data []string) {
	switch get_tag(term) {
	case LAM:
		chrs = append(chrs, '%')
		if get_tag(Lnk(ask_arg(mem, term, 0))) == ERA {
			chrs = append(chrs, '_')
		} else {
			chrs = append(chrs, 'x')
			readback_decimal(chrs, stk_find(vars, u64(Var(get_loc(term, 0)))))
		}
		chrs = append(chrs, ' ')
		readback_term(chrs, mem, Lnk(ask_arg(mem, term, 1)), vars, dirs, id_to_name_data)
		break
	case APP:
		chrs = append(chrs, '(')
		readback_term(chrs, mem, Lnk(ask_arg(mem, term, 0)), vars, dirs, id_to_name_data)
		chrs = append(chrs, ' ')
		readback_term(chrs, mem, Lnk(ask_arg(mem, term, 1)), vars, dirs, id_to_name_data)
		chrs = append(chrs, ')')
		break
	case PAR:
		col := get_ext(term)
		if len(dirs[col]) > 0 {
			head := stk_pop(dirs[col])
			if head == 0 {
				readback_term(chrs, mem, Lnk(ask_arg(mem, term, 0)), vars, dirs, id_to_name_data)
				dirs[col] = append(dirs[col], head)
			} else {
				readback_term(chrs, mem, Lnk(ask_arg(mem, term, 1)), vars, dirs, id_to_name_data)
				dirs[col] = append(dirs[col], head)
			}
		} else {
			chrs = append(chrs, '<')
			readback_term(chrs, mem, Lnk(ask_arg(mem, term, 0)), vars, dirs, id_to_name_data)
			chrs = append(chrs, ' ')
			readback_term(chrs, mem, Lnk(ask_arg(mem, term, 1)), vars, dirs, id_to_name_data)
			chrs = append(chrs, '>')
		}
		break
	case DP0:
	case DP1:
		col := get_ext(term)
		_ = ask_arg(mem, term, 2)
		pushVal := 0
		if get_tag(term) != DP0 {
			pushVal = 1
		}
		dirs[col] = append(dirs[col], u64(pushVal))
		readback_term(chrs, mem, Lnk(ask_arg(mem, term, 2)), vars, dirs, id_to_name_data)
		stk_pop(dirs[col])
		break
	case OP2:
		chrs = append(chrs, '(')
		readback_term(chrs, mem, Lnk(ask_arg(mem, term, 0)), vars, dirs, id_to_name_data)
		switch get_ext(term) {
		case ADD:
			chrs = append(chrs, '+')
		case SUB:
			chrs = append(chrs, '-')
		case MUL:
			chrs = append(chrs, '*')
		case DIV:
			chrs = append(chrs, '/')
		case MOD:
			chrs = append(chrs, '%')
		case AND:
			chrs = append(chrs, '&')
		case OR:
			chrs = append(chrs, '|')
		case XOR:
			chrs = append(chrs, '^')
		case SHL:
			chrs = append(chrs, '<')
			chrs = append(chrs, '<')
		case SHR:
			chrs = append(chrs, '>')
			chrs = append(chrs, '>')
		case LTN:
			chrs = append(chrs, '<')
		case LTE:
			chrs = append(chrs, '<')
			chrs = append(chrs, '=')
		case EQL:
			chrs = append(chrs, '=')
			chrs = append(chrs, '=')
		case GTE:
			chrs = append(chrs, '>')
			chrs = append(chrs, '=')
		case GTN:
			chrs = append(chrs, '>')
		case NEQ:
			chrs = append(chrs, '!')
			chrs = append(chrs, '=')
		}
		readback_term(chrs, mem, Lnk(ask_arg(mem, term, 1)), vars, dirs, id_to_name_data)
	case U32:
		readback_decimal(chrs, get_val(term))
	case CTR:
	case CAL:
		fun := get_ext(term)
		ari := get_ari(term)
		chrs = append(chrs, '(')
		if int(fun) < len(id_to_name_data) && id_to_name_data[fun] != "" {
			for _, v := range id_to_name_data[fun] {
				chrs = append(chrs, u64(v))
			}
		} else {
			chrs = append(chrs, '$')
			readback_decimal(chrs, fun)
		}
		for i := u64(0); i < ari; i++ {
			chrs = append(chrs, ' ')
			readback_term(chrs, mem, Lnk(ask_arg(mem, term, i)), vars, dirs, id_to_name_data)
		}
		chrs = append(chrs, ')')
	case VAR:
		chrs = append(chrs, 'x')
		readback_decimal(chrs, stk_find(vars, u64(term)))
	default:
		chrs = append(chrs, '?')
	}
}

func readback(code_mcap u64, mem *Worker, term Lnk, id_to_name_data []string) string {
	const dirs_mcap u64 = 65536
	var (
		seen = Stk{}
		chrs = Stk{}
		vars = Stk{}
		dirs = []Stk{}
	)
	stk_init(seen)
	stk_init(chrs)
	stk_init(vars)
	for i := 0; i < int(dirs_mcap); i++ {
		dirs = append(dirs, Stk{})
		stk_init(dirs[i])
	}

	readback_vars(vars, mem, term, seen)
	readback_term(chrs, mem, term, vars, dirs, id_to_name_data)
	code_data := ""
	for i := 0; i < len(chrs); i++ {
		code_data += fmt.Sprint(chrs[i])
	}
	return code_data
}

func debug_print_lnk(lnk Lnk) {
	tag := get_tag(lnk)
	ext := get_ext(lnk)
	val := get_val(lnk)
	str := ""
	switch tag {
	case DP0:
		str = "DP0"
	case DP1:
		str = "DP1"
	case VAR:
		str = "VAR"
	case ARG:
		str = "ARG"
	case ERA:
		str = "ERA"
	case LAM:
		str = "LAM"
	case APP:
		str = "APP"
	case PAR:
		str = "PAR"
	case CTR:
		str = "CTR"
	case CAL:
		str = "CAL"
	case OP2:
		str = "OP2"
	case U32:
		str = "U32"
	case F32:
		str = "F32"
	case NIL:
		str = "NIL"
	default:
		str = "???"
	}
	fmt.Printf("%s %x %x %x\n", str, ext, val, lnk)
}

func parse_arg(code string, id_to_name_data []string) Lnk {
	if code[0] >= '0' && code[0] <= '9' {
		i, _ := strconv.Atoi(code)
		return U_32(u64(i))
	}
	return U_32(0)
}

func main() {
	//	fmt.Println("HEAP_SIZE:", HEAP_SIZE, u64(unsafe.Sizeof(u64(0))))
	mem := Worker{}
	var (
		start time.Time
		stop  time.Time
	)

	// const u64 id_to_name_size = /* GENERATED_NAME_COUNT_CONTENT */
	// char* id_to_name_data[id_to_name_size];
	id_to_name_data := []string{
		/* GENERATED_ID_TO_NAME_DATA_CONTENT */
	}
	// builds main term
	mem.node = make([]Lnk, HEAP_SIZE)
	if len(os.Args) <= 1 {
		mem.node = append(mem.node, Cal(0, _MAIN_, 0))
	} else {
		mem.node = append(mem.node, Cal(u64(len(os.Args)-1), _MAIN_, 1))
		for _, arg := range os.Args[1:] {
			mem.node = append(mem.node, parse_arg(arg, id_to_name_data))
		}
	}
	// reduces and benchmarks
	start = time.Now()
	ffi_normal(mem.node, 0)
	stop = time.Now()

	// Prints result statistics
	// u64 delta_time = (stop.tv_sec - start.tv_sec) * 1000000 + stop.tv_usec - start.tv_usec;
	// double rwt_per_sec = (double)ffi_cost / (double)delta_time;
	fmt.Printf("Rewrites: %v (%.2f MR/s).\n", ffi_cost, float64(ffi_cost)/float64(stop.Sub(start).Seconds()))
	fmt.Printf("Mem.Size: %v words.\n", ffi_size)

	// Prints result normal form
	const code_mcap = u64(256 * 256 * 256) // max code size = 16 MB
	// char* code_data = (char*)malloc(code_mcap * sizeof(char));
	code_data := readback(code_mcap, &mem, mem.node[0], id_to_name_data)
	fmt.Println(code_data)
}
