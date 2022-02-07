package main

import (
	"fmt"
	"os"
	"strconv"
)

// Constants
// ---------

const (
	U64_PER_KB uint64 = 0x80
	U64_PER_MB uint64 = 0x20000
	U64_PER_GB uint64 = 0x8000000

	MAX_ARITY uint64 = 16
	MEM_SPACE uint64 = U64_PER_GB

	SEEN_SIZE        = 4194304
	VAL       uint64 = 1
	EXT       uint64 = 0x100000000
	ARI       uint64 = 0x100000000000000
	TAG       uint64 = 0x1000000000000000

	DP0 uint64 = 0x0
	DP1 uint64 = 0x1
	VAR uint64 = 0x2
	ARG uint64 = 0x3
	ERA uint64 = 0x4
	LAM uint64 = 0x5
	APP uint64 = 0x6
	PAR uint64 = 0x7
	CTR uint64 = 0x8
	CAL uint64 = 0x9
	OP2 uint64 = 0xA
	U32 uint64 = 0xB
	F32 uint64 = 0xC
	OUT uint64 = 0xE
	NIL uint64 = 0xF

	ADD uint64 = 0x0
	SUB uint64 = 0x1
	MUL uint64 = 0x2
	DIV uint64 = 0x3
	MOD uint64 = 0x4
	AND uint64 = 0x5
	OR  uint64 = 0x6
	XOR uint64 = 0x7
	SHL uint64 = 0x8
	SHR uint64 = 0x9
	LTN uint64 = 0xA
	LTE uint64 = 0xB
	EQL uint64 = 0xC
	GTE uint64 = 0xD
	GTN uint64 = 0xE
	NEQ uint64 = 0xF
)

//GENERATED_CONSTRUCTOR_IDS_START//
/* GENERATED_CONSTRUCTOR_IDS_CONTENT */
//GENERATED_CONSTRUCTOR_IDS_END//

// Types
// -----

type Lnk uint64
type Rewriter func(*Worker, uint64, Lnk) bool

type Function struct {
	Stricts  []uint64
	Rewriter Rewriter
	Arity    uint64
}

type Worker struct {
	Node []Lnk
	Free map[uint64][]uint64
	Size uint64
	Cost uint64
}

func NewWorker() *Worker {
	return &Worker{
		Node: make([]Lnk, 0, U64_PER_GB),
		Free: make(map[uint64][]uint64, 0),
		Size: 0,
		Cost: 0,
	}
}

// Globals
// -------

var (
	SeenData map[uint64]uint64
)

// Constructors

func Var(pos uint64) Lnk {
	return Lnk((VAR * TAG) | pos)
}

func Dp0(col, pos uint64) Lnk {
	return Lnk((DP0 * TAG) | (col * EXT) | pos)
}

func Dp1(col, pos uint64) Lnk {
	return Lnk((DP1 * TAG) | (col * EXT) | pos)
}

func Arg(pos uint64) Lnk {
	return Lnk((ARG * TAG) | pos)
}

func Era() Lnk {
	return Lnk(ERA * TAG)
}

func Lam(pos uint64) Lnk {
	return Lnk((LAM * TAG) | pos)
}

func App(pos uint64) Lnk {
	return Lnk((APP * TAG) | pos)
}

func Par(col, pos uint64) Lnk {
	return Lnk((PAR * TAG) | (col * EXT) | pos)
}

func Op2(ope, pos uint64) Lnk {
	return Lnk((OP2 * TAG) | (ope * EXT) | pos)
}

func U_32(val uint64) Lnk {
	return Lnk((U32 * TAG) | val)
}

func Nil() Lnk {
	return Lnk(NIL * TAG)
}

func Ctr(ari, fun, pos uint64) Lnk {
	return Lnk((CTR * TAG) | (ari * ARI) | (fun * EXT) | pos)
}

func Cal(ari, fun, pos uint64) Lnk {
	return Lnk((CAL * TAG) | (ari * ARI) | (fun * EXT) | pos)
}

func Out(arg, fld uint64) Lnk {
	return Lnk((OUT * TAG) | (arg << 8) | fld)
}

// Getters
// -------

func get_tag(lnk Lnk) uint64 {
	return uint64(lnk) / TAG
}

func get_ext(lnk Lnk) uint64 {
	return uint64(lnk) / EXT & 0xFFFFFF
}

func get_val(lnk Lnk) uint64 {
	return uint64(lnk) & 0xFFFFFFFF
}

func get_ari(lnk Lnk) uint64 {
	return uint64(lnk) / ARI & 0xF
}

func get_loc(lnk Lnk, arg uint64) uint64 {
	return get_val(lnk) + arg
}

// Memory
// ------

func ask_lnk(mem *Worker, loc uint64) Lnk {
	return mem.Node[loc]
}

func ask_arg(mem *Worker, term Lnk, arg uint64) Lnk {
	return ask_lnk(mem, get_loc(term, arg))
}

func link(mem *Worker, loc uint64, lnk Lnk) Lnk {
	mem.Node[loc] = lnk
	if get_tag(lnk) <= VAR {
		pos := get_loc(lnk, get_tag(lnk)&0x01)
		mem.Node[pos] = Arg(loc)
	}
	return lnk
}

func alloc(mem *Worker, size uint64) uint64 {
	if size == 0 {
		return 0
	}
	if len(mem.Free) > int(size) && len(mem.Free[size]) > 0 {
		reuse := mem.Free[size][len(mem.Free[size])-1]
		mem.Free[size] = mem.Free[size][:len(mem.Free[size])-1]
		return reuse
	}
	loc := uint64(len(mem.Node))
	mem.Node = append(mem.Node, make([]Lnk, size)...)
	return loc
}

func clear(mem *Worker, loc, size uint64) {
	if len(mem.Free) > int(size) && mem.Free[size] == nil {
		mem.Free[size] = []uint64{}
	}
	mem.Free[size] = append(mem.Free[size], loc)
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
		if get_tag(ask_arg(mem, term, 0)) != ERA {
			link(mem, get_loc(ask_arg(mem, term, 0), 0), Era())
		}
		collect(mem, ask_arg(mem, term, 1))
		clear(mem, get_loc(term, 0), 2)
	case APP:
		collect(mem, ask_arg(mem, term, 0))
		collect(mem, ask_arg(mem, term, 1))
		clear(mem, get_loc(term, 0), 2)
	case PAR:
		collect(mem, ask_arg(mem, term, 0))
		collect(mem, ask_arg(mem, term, 1))
		clear(mem, get_loc(term, 0), 2)
	case OP2:
		collect(mem, ask_arg(mem, term, 0))
		collect(mem, ask_arg(mem, term, 1))
	case U32:
		break
	case CTR:
		arity := get_ari(term)
		for i := uint64(0); i < arity; i++ {
			collect(mem, ask_arg(mem, term, i))
		}
		clear(mem, get_loc(term, 0), arity)
	case CAL:
		arity := get_ari(term)
		for i := uint64(0); i < arity; i++ {
			collect(mem, ask_arg(mem, term, i))
		}
		clear(mem, get_loc(term, 0), arity)
	default:
		break
	}
}

func inc_cost(mem *Worker) {
	mem.Cost++
}

// Reduction
// ---------

func subst(mem *Worker, lnk, val Lnk) {
	if get_tag(lnk) != ERA {
		link(mem, get_loc(lnk, 0), val)
	} else {
		collect(mem, val)
	}
}

func cal_par(mem *Worker, host uint64, term Lnk, argn Lnk, n uint64) Lnk {
	inc_cost(mem)
	arit := get_ari(term)
	fun := get_ext(term)
	fun0 := get_loc(term, 0)
	fun1 := alloc(mem, arit)
	par0 := get_loc(argn, 0)
	for i := uint64(0); i < arit; i++ {
		if i != n {
			leti := alloc(mem, 3)
			argi := ask_arg(mem, term, i)
			link(mem, fun0+i, Dp0(get_ext(argn), leti))
			link(mem, fun1+i, Dp1(get_ext(argn), leti))
			link(mem, leti+2, argi)
		} else {
			link(mem, fun0+i, ask_arg(mem, argn, 0))
			link(mem, fun1+i, ask_arg(mem, argn, 1))
		}
	}
	link(mem, par0+0, Cal(arit, fun, fun0))
	link(mem, par0+1, Cal(arit, fun, fun1))
	done := Par(get_ext(argn), par0)
	link(mem, host, done)
	return done
}

func reduce(
	mem *Worker,
	funcs []Function,
	root uint64,
	_opt_id_to_name *map[uint64]string,
	debug bool,
) Lnk {
	stack := []uint64{}
	init := uint64(1)
	host := root
	for {
		term := ask_lnk(mem, host)
		if debug {
			fmt.Println("-----------------")
			fmt.Printf("%v\n", show_term(mem, ask_lnk(mem, root), _opt_id_to_name, uint64(term)))
		}
		if init == 1 {
			switch get_tag(term) {
			case APP:
				stack = append(stack, host)
				init = 1
				host = get_loc(term, 0)
				continue
			case DP0:
				stack = append(stack, host)
				host = get_loc(term, 2)
				continue
			case DP1:
				stack = append(stack, host)
				host = get_loc(term, 2)
				continue
			case OP2:
				stack = append(stack, host)
				stack = append(stack, get_loc(term, 1)|0x80000000)
				host = get_loc(term, 0)
				continue
			case CAL:
				fun := get_ext(term)
				// ari := get_ari(term)
				// if len(funcs) > int(fun) {
				switch fun {
				//GENERATED_REWRITE_RULES_STEP_0_START//
				/* GENERATED_REWRITE_RULES_STEP_0_CONTENT */
				//GENERATED_REWRITE_RULES_STEP_0_END//
				}
				// }
			default:
				break
			}
		} else {
			switch get_tag(term) {
			case APP:
				arg0 := ask_arg(mem, term, 0)
				if get_tag(arg0) == LAM {
					inc_cost(mem)
					subst(mem, ask_arg(mem, arg0, 0), ask_arg(mem, term, 1))
					_ = link(mem, host, ask_arg(mem, arg0, 1))
					clear(mem, get_loc(term, 0), 2)
					clear(mem, get_loc(arg0, 0), 2)
					init = 1
					continue
				}
				if get_tag(arg0) == PAR {
					inc_cost(mem)
					app0 := get_loc(term, 0)
					app1 := get_loc(arg0, 0)
					let0 := alloc(mem, 3)
					par0 := alloc(mem, 2)
					link(mem, let0+2, ask_arg(mem, term, 1))
					link(mem, app0+1, Dp0(get_ext(arg0), let0))
					link(mem, app0+0, ask_arg(mem, arg0, 0))
					link(mem, app1+0, ask_arg(mem, arg0, 1))
					link(mem, app1+1, Dp1(get_ext(arg0), let0))
					link(mem, par0+0, App(app0))
					link(mem, par0+1, App(app1))
					done := Par(get_ext(arg0), par0)
					link(mem, host, done)
				}
			case DP0 | DP1:
				arg0 := ask_arg(mem, term, 2)
				if get_tag(arg0) == LAM {
					inc_cost(mem)
					let0 := get_loc(term, 0)
					par0 := get_loc(arg0, 0)
					lam0 := alloc(mem, 2)
					lam1 := alloc(mem, 2)
					link(mem, let0+2, ask_arg(mem, arg0, 1))
					link(mem, par0+1, Var(lam1))
					arg0_arg_0 := ask_arg(mem, arg0, 0)
					link(mem, par0+0, Var(lam0))
					subst(mem, arg0_arg_0, Par(get_ext(term), par0))
					term_arg_0 := ask_arg(mem, term, 0)
					link(mem, lam0+1, Dp0(get_ext(term), let0))
					subst(mem, term_arg_0, Lam(lam0))
					term_arg_1 := ask_arg(mem, term, 1)
					link(mem, lam1+1, Dp1(get_ext(term), let0))
					subst(mem, term_arg_1, Lam(lam1))
					done := Lam(lam1)
					if get_tag(term) == DP0 {
						done = Lnk(lam0)
					}
					link(mem, host, done)
					init = 1
					continue
				} else if get_tag(arg0) == PAR {
					if get_ext(term) == get_ext(arg0) {
						inc_cost(mem)
						subst(mem, ask_arg(mem, term, 0), ask_arg(mem, arg0, 0))
						subst(mem, ask_arg(mem, term, 1), ask_arg(mem, arg0, 1))
						arg := uint64(0)
						if get_tag(term) == DP0 {
							arg = 0
						} else {
							arg = 1
						}
						_ = link(mem, host, ask_arg(mem, arg0, arg))
						clear(mem, get_loc(term, 0), 3)
						clear(mem, get_loc(arg0, 0), 2)
						init = 1
						continue
					} else {
						inc_cost(mem)
						par0 := alloc(mem, 2)
						let0 := get_loc(term, 0)
						par1 := get_loc(arg0, 0)
						let1 := alloc(mem, 3)
						link(mem, let0+2, ask_arg(mem, arg0, 0))
						link(mem, let1+2, ask_arg(mem, arg0, 1))
						term_arg_0 := ask_arg(mem, term, 0)
						term_arg_1 := ask_arg(mem, term, 1)
						link(mem, par1+0, Dp1(get_ext(term), let0))
						link(mem, par1+1, Dp1(get_ext(term), let1))
						link(mem, par0+0, Dp0(get_ext(term), let0))
						link(mem, par0+1, Dp0(get_ext(term), let1))
						subst(mem, term_arg_0, Par(get_ext(arg0), par0))
						subst(mem, term_arg_1, Par(get_ext(arg0), par1))
						parN := uint64(0)
						if get_tag(term) == DP0 {
							parN = par0
						} else {
							parN = par1
						}
						done := Par(get_ext(arg0), parN)
						link(mem, host, done)
					}
				} else if get_tag(arg0) == U32 {
					inc_cost(mem)
					subst(mem, ask_arg(mem, term, 0), arg0)
					subst(mem, ask_arg(mem, term, 1), arg0)
					link(mem, host, arg0)
				} else if get_tag(arg0) == CTR {
					inc_cost(mem)
					fun := get_ext(arg0)
					ari := get_ari(arg0)
					if ari == 0 {
						subst(mem, ask_arg(mem, term, 0), Ctr(0, fun, 0))
						subst(mem, ask_arg(mem, term, 1), Ctr(0, fun, 0))
						clear(mem, get_loc(term, 0), 3)
						link(mem, host, Ctr(0, fun, 0))
					} else {
						ctr0 := get_loc(arg0, 0)
						ctr1 := alloc(mem, ari)
						for i := uint64(0); i < ari-1; i++ {
							leti := alloc(mem, 3)
							link(mem, leti+2, ask_arg(mem, arg0, i))
							link(mem, ctr0, Dp0(get_ext(term), leti))
							link(mem, ctr1, Dp1(get_ext(term), leti))
						}
						leti := get_loc(term, 0)
						link(mem, leti+2, ask_arg(mem, arg0, ari-1))
						term_arg_0 := ask_arg(mem, term, 0)
						link(mem, ctr0+ari-1, Dp0(get_ext(term), leti))
						subst(mem, term_arg_0, Ctr(0, fun, ctr0))
						term_arg_1 := ask_arg(mem, term, 0)
						link(mem, ctr1+ari-1, Dp1(get_ext(term), leti))
						subst(mem, term_arg_1, Ctr(0, fun, ctr1))
						arg := ctr1
						if get_tag(term) == DP0 {
							arg = ctr0
						}
						done := Ctr(ari, fun, arg)
						link(mem, host, done)
					}
				}
			case OP2:
				arg0 := ask_arg(mem, term, 0)
				arg1 := ask_arg(mem, term, 1)
				if get_tag(arg0) == U32 && get_tag(arg1) == U32 {
					inc_cost(mem)
					a := get_val(arg0)
					b := get_val(arg1)
					c := uint64(0)
					switch get_ext(term) {
					case ADD:
						c = a + b&0xFFFFFFFF
					case SUB:
						c = a - b&0xFFFFFFFF
					case MUL:
						c = a * b & 0xFFFFFFFF
					case DIV:
						c = a / b & 0xFFFFFFFF
					case MOD:
						c = a % b & 0xFFFFFFFF
					case AND:
						c = a & b & 0xFFFFFFFF
					case OR:
						c = a | b&0xFFFFFFFF
					case XOR:
						c = a ^ b&0xFFFFFFFF
					case SHL:
						c = a << b & 0xFFFFFFFF
					case SHR:
						c = a >> b & 0xFFFFFFFF
					case LTN:
						if a < b {
							c = 1
						} else {
							c = 0
						}
					case LTE:
						if a <= b {
							c = 1
						} else {
							c = 0
						}
					case EQL:
						if a == b {
							c = 1
						} else {
							c = 0
						}
					case GTE:
						if a >= b {
							c = 1
						} else {
							c = 0
						}
					case GTN:
						if a > b {
							c = 1
						} else {
							c = 0
						}
					case NEQ:
						if a != b {
							c = 1
						} else {
							c = 0
						}
					default:
						c = 0
					}
					done := U_32(c)
					clear(mem, get_loc(term, 0), 2)
					link(mem, host, done)
				} else if get_tag(arg0) == PAR {
					inc_cost(mem)
					op20 := get_loc(term, 0)
					op21 := get_loc(arg0, 0)
					let0 := alloc(mem, 3)
					par0 := alloc(mem, 2)
					link(mem, let0+2, arg1)
					link(mem, op20+1, Dp0(get_ext(arg0), let0))
					link(mem, op20+0, ask_arg(mem, arg0, 0))
					link(mem, op21+0, ask_arg(mem, arg0, 1))
					link(mem, op21+1, Dp1(get_ext(arg0), let0))
					link(mem, par0+0, Op2(get_ext(term), op20))
					link(mem, par0+1, Op2(get_ext(term), op21))
					done := Par(get_ext(arg0), par0)
					link(mem, host, done)
				} else if get_tag(arg1) == PAR {
					inc_cost(mem)
					op20 := get_loc(term, 0)
					op21 := get_loc(arg1, 0)
					let0 := alloc(mem, 3)
					par0 := alloc(mem, 2)
					link(mem, let0+2, arg0)
					link(mem, op20+0, Dp0(get_ext(arg1), let0))
					link(mem, op20+1, ask_arg(mem, arg1, 0))
					link(mem, op21+1, ask_arg(mem, arg1, 1))
					link(mem, op21+0, Dp1(get_ext(arg1), let0))
					link(mem, par0+0, Op2(get_ext(term), op20))
					link(mem, par0+1, Op2(get_ext(term), op21))
					done := Par(get_ext(arg1), par0)
					link(mem, host, done)
				}
			case CAL:
				fun := get_ext(term)
				// ari := get_ari(term)
				switch fun {
					//GENERATED_REWRITE_RULES_STEP_1_START//
/* GENERATED_REWRITE_RULES_STEP_1_CONTENT */
					//GENERATED_REWRITE_RULES_STEP_1_END//
				}
			default:
				break
			}
		}
		if len(stack) > 0 {
			item := stack[len(stack)-1]
			init = item >> 31
			host = item & 0x7FFFFFFF
			continue
		}
		break
	}
	return ask_lnk(mem, root)
}

func set_seen(m map[uint64]bool, key uint64) {
	m[key] = true
}

func get_seen(m map[uint64]bool, key uint64) bool {
	val, ok := m[key]
	return ok && val
}

func normal_go(
	mem *Worker,
	funcs []Function,
	host uint64,
	seen map[uint64]bool,
	opt_id_to_name *map[uint64]string,
	debug bool,
) Lnk {
	term := ask_lnk(mem, host)
	if get_seen(seen, host) {
		return term
	}
	term = reduce(mem, funcs, host, opt_id_to_name, debug)
	set_seen(seen, host)
	rec_locs := []uint64{}
	switch get_tag(term) {
	case LAM:
		rec_locs = append(rec_locs, get_loc(term, 1))
	case APP:
		rec_locs = append(rec_locs, get_loc(term, 0))
		rec_locs = append(rec_locs, get_loc(term, 1))
	case PAR:
		rec_locs = append(rec_locs, get_loc(term, 0))
	case DP0:
		rec_locs = append(rec_locs, get_loc(term, 2))
	case DP1:
		rec_locs = append(rec_locs, get_loc(term, 2))
	case CTR:
		arity := get_ari(term)
		for i := uint64(0); i < arity; i++ {
			rec_locs = append(rec_locs, get_loc(term, i))
		}
	case CAL:
		arity := get_ari(term)
		for i := uint64(0); i < arity; i++ {
			rec_locs = append(rec_locs, get_loc(term, i))
		}
	default:
		break
	}
	for _, loc := range rec_locs {
		lnk := normal_go(mem, funcs, loc, seen, opt_id_to_name, debug)
		link(mem, loc, lnk)
	}
	return term
}

func normal(
	mem *Worker,
	host uint64,
	funcs []Function,
	opt_id_to_name *map[uint64]string,
	debug bool,
) Lnk {
	seen := map[uint64]bool{}
	return normal_go(mem, funcs, host, seen, opt_id_to_name, debug)
}

// Debug
// -----

func show_lnk(x Lnk) string {
	if x == 0 {
		return "~"
	}
	tag := get_tag(x)
	ext := get_ext(x)
	val := get_val(x)
	ari := ""
	switch tag {
	case CTR:
		ari = fmt.Sprintf("%d", get_ari(x))
	case CAL:
		ari = fmt.Sprintf("%d", get_ari(x))
	}
	tgs := "???"
	switch tag {
	case DP0:
		tgs = "DP0"
	case DP1:
		tgs = "DP1"
	case VAR:
		tgs = "VAR"
	case ARG:
		tgs = "ARG"
	case ERA:
		tgs = "ERA"
	case LAM:
		tgs = "LAM"
	case APP:
		tgs = "APP"
	case PAR:
		tgs = "PAR"
	case CTR:
		tgs = "CTR"
	case CAL:
		tgs = "CAL"
	case OP2:
		tgs = "OP2"
	case U32:
		tgs = "U32"
	case F32:
		tgs = "F32"
	case OUT:
		tgs = "OUT"
	case NIL:
		tgs = "NIL"
	}
	return fmt.Sprintf("%v%v:%x:%x", tgs, ari, ext, val)
}

func show_mem(mem *Worker) string {
	s := ""
	for i := 0; i < len(mem.Node); i++ {
		s += fmt.Sprintf("%x |\n", i) + show_lnk(mem.Node[i])
		if i >= 48 {
			break
		}
	}
	return s
}

func show_term(
	mem *Worker,
	term Lnk,
	opt_id_to_name *map[uint64]string,
	focus uint64,
) string {
	lets := map[uint64]uint64{}
	kinds := map[uint64]uint64{}
	names := map[uint64]string{}
	count := uint64(0)
	var find_lets func(mem *Worker, term Lnk, lets, kinds *map[uint64]uint64, names *map[uint64]string, count *uint64)
	find_lets = func(mem *Worker, term Lnk, lets, kinds *map[uint64]uint64, names *map[uint64]string, count *uint64) {
		switch get_tag(term) {
		case LAM:
			(*names)[get_loc(term, 0)] = fmt.Sprintf("%d", count)
			*count++
			find_lets(mem, ask_arg(mem, term, 1), lets, kinds, names, count)
		case APP:
			find_lets(mem, ask_arg(mem, term, 0), lets, kinds, names, count)
			find_lets(mem, ask_arg(mem, term, 1), lets, kinds, names, count)
		case PAR:
			find_lets(mem, ask_arg(mem, term, 0), lets, kinds, names, count)
			find_lets(mem, ask_arg(mem, term, 1), lets, kinds, names, count)
		case DP0:
			if _, ok := (*lets)[get_loc(term, 0)]; !ok {
				(*names)[get_loc(term, 0)] = fmt.Sprintf("%d", count)
				*count++
				(*kinds)[get_loc(term, 0)] = get_ext(term)
				find_lets(mem, ask_arg(mem, term, 2), lets, kinds, names, count)
			}
		case DP1:
			if _, ok := (*lets)[get_loc(term, 0)]; !ok {
				(*names)[get_loc(term, 0)] = fmt.Sprintf("%d", count)
				*count++
				(*kinds)[get_loc(term, 0)] = get_ext(term)
				find_lets(mem, ask_arg(mem, term, 2), lets, kinds, names, count)
			}
		case OP2:
			find_lets(mem, ask_arg(mem, term, 0), lets, kinds, names, count)
			find_lets(mem, ask_arg(mem, term, 1), lets, kinds, names, count)
		case CTR:
			arity := get_ari(term)
			for i := uint64(0); i < arity; i++ {
				find_lets(mem, ask_arg(mem, term, i), lets, kinds, names, count)
			}
		case CAL:
			arity := get_ari(term)
			for i := uint64(0); i < arity; i++ {
				find_lets(mem, ask_arg(mem, term, i), lets, kinds, names, count)
			}
		default:
			break
		}
	}
	var _go func(*Worker, Lnk, *map[uint64]string, *map[uint64]string, *uint64) string
	_go = func(mem *Worker, term Lnk, names *map[uint64]string, opt_id_to_name *map[uint64]string, focus *uint64) string {
		done := ""
		switch get_tag(term) {
		case DP0:
			v, ok := (*names)[get_loc(term, 0)]
			if !ok {
				v = "?"
			}
			done = fmt.Sprintf("a%v", v)
		case DP1:
			v, ok := (*names)[get_loc(term, 0)]
			if !ok {
				v = "?"
			}
			done = fmt.Sprintf("b%v", v)
		case VAR:
			v, ok := (*names)[get_loc(term, 0)]
			if !ok {
				v = "?"
			}
			done = fmt.Sprintf("x%v", v)
		case LAM:
			v, ok := (*names)[get_loc(term, 0)]
			if !ok {
				v = "?"
			}
			done = "λ" + v + " " + _go(mem, ask_arg(mem, term, 1), names, opt_id_to_name, focus)
		case APP:
			fun := _go(mem, ask_arg(mem, term, 0), names, opt_id_to_name, focus)
			argm := _go(mem, ask_arg(mem, term, 1), names, opt_id_to_name, focus)
			done = "(" + fun + " " + argm + ")"
		case OP2:
			oper := get_ext(term)
			val0 := _go(mem, ask_arg(mem, term, 0), names, opt_id_to_name, focus)
			val1 := _go(mem, ask_arg(mem, term, 1), names, opt_id_to_name, focus)
			symb := "?"
			switch oper {
			case 0x00:
				symb = "+"
			case 0x01:
				symb = "-"
			case 0x02:
				symb = "*"
			case 0x03:
				symb = "/"
			case 0x04:
				symb = "%"
			case 0x05:
				symb = "&"
			case 0x06:
				symb = "|"
			case 0x07:
				symb = "^"
			case 0x08:
				symb = "<<"
			case 0x09:
				symb = ">>"
			case 0x10:
				symb = "<"
			case 0x11:
				symb = "<="
			case 0x12:
				symb = "="
			case 0x13:
				symb = ">="
			case 0x14:
				symb = ">"
			case 0x15:
				symb = "!="
			}
			done = "(" + val0 + " " + symb + " " + val1 + ")"
		case U32:
			done = fmt.Sprint(get_val(term))
		case CTR:
			fun := get_ext(term)
			arity := get_ari(term)
			args := make([]string, arity)
			for i := uint64(0); i < arity; i++ {
				args[i] = _go(mem, ask_arg(mem, term, i), names, opt_id_to_name, focus)
			}
			name := "?"
			if v, ok := (*opt_id_to_name)[fun]; ok {
				name = v
			} else {
				if get_tag(term) < CAL {
					name = "C"
				} else {
					name = "F"
				}
				name += fmt.Sprint(fun)
			}
			done := "(" + name
			for _, v := range args {
				done += " " + v
			}
			done += ")"
		case CAL:
			fun := get_ext(term)
			arity := get_ari(term)
			args := make([]string, arity)
			for i := uint64(0); i < arity; i++ {
				args[i] = _go(mem, ask_arg(mem, term, i), names, opt_id_to_name, focus)
			}
			name := "?"
			if v, ok := (*opt_id_to_name)[fun]; ok {
				name = v
			} else {
				if get_tag(term) < CAL {
					name = "C"
				} else {
					name = "F"
				}
				name += fmt.Sprint(fun)
			}
			done := "(" + name
			for _, v := range args {
				done += " " + v
			}
			done += ")"
		}
		if uint64(term) == *focus {
			return "$" + done
		}
		return done
	}
	find_lets(mem, term, &lets, &kinds, &names, &count)
	text := _go(mem, term, &names, opt_id_to_name, &focus)
	for _, pos := range lets {
		name, ok := names[pos]
		if !ok {
			name = "?"
		}
		nam0 := "a" + name
		if ask_lnk(mem, pos+0) == Era() {
			nam0 = "*"
		}
		nam1 := "b" + name
		if ask_lnk(mem, pos+1) == Era() {
			nam1 = "*"
		}
		text += fmt.Sprintf("\n dup %v %v = %v;", nam0, nam1, _go(mem, ask_lnk(mem, pos+2), &names, opt_id_to_name, &focus), focus)
	}
	return text
}

func parse_arg(code string, id_to_name_data []string) Lnk {
	if code[0] >= '0' && code[0] <= '9' {
		i, _ := strconv.Atoi(code)
		return U_32(uint64(i))
	}
	return U_32(0)
}

func read_memory(mem *Worker) {
	for i := 0; i < len(mem.Node); i++ {
		fmt.Println(show_lnk(mem.Node[i]))
	}
}

func main() {
	var mem *Worker = NewWorker()
	// var focus uint64
	// var opt_id_to_name map[uint64]string
	var names map[uint64]string = map[uint64]string{}
	// var lets []uint64
	// var kinds []uint64
	// var count uint64
	var (
		mangleNames = []string{
			/* GENERATED_ID_TO_NAME_DATA_CONTENT */
		}
	)
	for i, name := range mangleNames {
		names[uint64(i)] = name
	}
	const threads = /* GENERATED_NUM_THREADS_CONTENT */
	if len(os.Args) <= 1 {
		mem.Node = append(mem.Node, Cal(0, _MAIN_, 0))
	} else {
		mem.Node = append(mem.Node, Cal(uint64(len(os.Args)-1), _MAIN_, 1))
		for _, arg := range os.Args[1:] {
			mem.Node = append(mem.Node, parse_arg(arg, mangleNames))
		}
	}
	read_memory(mem)
	term := normal(mem, 0, []Function{}, &names, false)
	read_memory(mem)
	// show_term(mem, term, &map[uint64]string{}, 0)
	fmt.Println(show_lnk(term))
}

// const C_NAME_COUNT_CONTENT: &str = "/* GENERATED_NAME_COUNT_CONTENT */";
// const C_ID_TO_NAME_DATA_CONTENT: &str = "";
// const C_NUM_THREADS_CONTENT: &str = "/* GENERATED_NUM_THREADS_CONTENT */";
