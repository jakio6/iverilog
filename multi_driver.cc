/*
 * 多驱动检查 -- eda20426
 * */
#include "ivl_target.h"
#include "ivl_assert.h"
#include "netmisc.h"
#include "netlist.h"
#include "compiler.h"
#include "functor.h"
#include "nettypes.h"

#include "assign.h"

/* variables {{{*/

static proc all_assigns;
static int current_blk_id;
static const NetAssignBase *current_assign;
static const NetScope *current_scope;

// current step variables
static std::map<const NetNet *, const NetEConst *> env;
/*}}}*/
/* ... {{{*/
static void decode_range(std::vector<netrange_t>& ret, const NetNet *sig, const netrange_t &r);
static NetExpr* copy_replace(const NetExpr *expr, const std::map<const NetNet*, const NetEConst*>&vm);
static NetEConst* eval_with(const NetExpr *expr, const std::map<const NetNet*, const NetEConst*>&vm);
static std::string& get_scope_name(const void* scp);
/*}}}*/
/* multi driver check functor{{{*/
class multi_driver_f : public functor_t {
public:
	void process(Design *des, NetProcTop *ev);
};
/*}}}*/
/* output function {{{*/
static int
mdriven_cb(const void *sig_, const std::set<assign_info_t> &assigns,
		      const std::vector<netrange_t> &ranges)
{
	auto sig = static_cast<const NetNet*>(sig_);
	cout << "Multi-driver check: " << sig->name();
	for (auto const &it : ranges) {
		long l = it.get_msb();
		long r = it.get_lsb();
		if (l == r) {
			cout << ", " << l;
		} else {
			cout << ", " << l << ":" << r;
		}
	}

	cout << ",";

	// assigns的key为<NetScope*,NetAssignBase*>, 已经按照scope排序了.
	// 判断是否有在多个scope.
	bool multi_scope =
		(assigns.size() > 1 &&
		 assigns.begin()->first != assigns.rbegin()->first);

	for (auto const &as_ : assigns) {
		auto as = static_cast<const NetAssignBase*>(as_.second);
		cout << " " << as->get_file();
		if (multi_scope) {
			cout << ", " << get_scope_name(as_.first);
		}
		cout << ", #" << as->get_lineno() << ";";
	}
	cout << endl;
	return 0;
}

// avoid rebuilding scopes
static std::string&
get_scope_name(const void* scp)
{
	static std::map<const void *, std::string> scope_to_str;

	auto it = scope_to_str.find(scp);
	if (it != scope_to_str.end())
		return it->second;

	auto s = static_cast<const NetScope*>(scp);
	assert(s);

	std::string self = s->basename().str();
	if (s->parent())
		self = get_scope_name(s->parent()) + "." + self;

	scope_to_str[scp] = self;
	return scope_to_str[scp];
}

static int
cb_wrapper(const void *sig_, const std::set<assign_info_t> &assigns, long start, long end)
{
	auto sig = static_cast<const NetNet*>(sig_);
	std::vector<netrange_t> ranges;
	decode_range(ranges, sig, netrange_t(end, start));
	mdriven_cb(sig, assigns, ranges);
	return 0;
}
/*}}}*/
/* entry {{{*/
static void collect_block(const NetProcTop* net)
{
	// identify all initial blks with blk_id 0
	// all always blks owns a unique blk_id
	// assign from blk with different blk_id is multi driver.
	static int blk_count;

	// not all the cases pass this check.. who cares.
	// net->statement()->check_synth(net->type(), net->scope());
	if (debug_multi_driver_check)
		cerr << net->scope()->fullname();
	current_scope = net->scope();
	while (current_scope->type() != NetScope::MODULE) {
		current_scope = current_scope->parent();
	}
	switch (net->type()){
	case IVL_PR_INITIAL:
		current_blk_id = 0;
		net->statement()->multi_driver_check();
		break;
	case IVL_PR_ALWAYS:
		current_blk_id = ++blk_count;
		net->statement()->multi_driver_check();
		break;
	default:
		ivl_assert(*net, !"Unknown NetProcTop type");
		break;
	}
}

void
multi_driver_f::process(Design*, NetProcTop* net)
{
	collect_block(net);
}

/* entry point for multi driver check */
void
multi_driver (Design* des)
{
	multi_driver_f fun;
	all_assigns = proc();
	all_assigns.set_cb(cb_wrapper);

	des->functor(&fun);

	all_assigns.merge();
	all_assigns.report_conflict();
}
/*}}}*/
/* encode into/decode from a long integer {{{*/
/*
 * 将所有的word select, bit select, part select统一encode到一个bit range. 方便处理.
 * */
static netrange_t
encode_range(const NetNet *sig, long word, long base, long wid)
{
	unsigned vect_wid = sig->vector_width();
	long from = word * vect_wid + base;
	long to = from + wid-1;

	assert(from <= to);

	// msb, lsb
	return netrange_t(to, from);
}

static netrange_t
encode_full_range(const NetNet *sig) {
	// word is always start from zero
	return netrange_t(sig->vector_width() * sig->unpacked_count() - 1, 0);
}

static void
make_strides(const vector<netrange_t>&dims,
	     vector<long>&stride)
{
      stride[dims.size()-1] = 1;
      for (size_t idx = stride.size()-1 ; idx > 0 ; --idx) {
	    long tmp = dims[idx].width();
	    if (idx < stride.size())
		  tmp *= stride[idx];
	    stride[idx-1] = tmp;
      }
}

static void
decode_range(std::vector<netrange_t> &ret,
	     const NetNet *sig, const netrange_t &r) // output
{
	bool little = false;

	const unsigned long vec_wid = sig->vector_width();
	const std::vector<netrange_t> &dims = sig->packed_dims();
	const std::vector<netrange_t> &udims = sig->unpacked_dims();
	const netrange_t *vec_range = 0;

	if (r.width() > sig->vector_width()) {
		ret.insert(ret.end(), udims.rbegin(), udims.rend());
		ret.insert(ret.end(), dims.rbegin(), dims.rend());
		return;
	}

	if (dims.size() > 0) {
		// XXX: can verilog have multiple packed dims?
		vec_range = &dims[0];
	}

	little = vec_range && (vec_range->get_msb() < vec_range->get_lsb());

	// 一次assign最多不超过一个vector width.
	long word, base, wid;

	word = r.get_lsb() / vec_wid;
	base = r.get_lsb() - word * vec_wid;
	wid = (r.get_msb() - r.get_lsb()) % vec_wid;

	if (little) {
		base = vec_wid - base - 1;
		wid = -wid;
		base = base + vec_range->get_msb();
	} else if (vec_range) {
		base = base + vec_range->get_lsb();
	}

	if (udims.size() > 0) {
		vector<long> stride(udims.size());
		make_strides(udims, stride);
		long tmp = word;
		for (size_t i = 0; i < stride.size(); i++) {
			tmp = word / stride[i];
			word = word % stride[i];
			if (udims[i].get_lsb() < udims[i].get_msb())
				tmp = tmp + udims[i].get_lsb();
			else
				tmp = tmp + udims[i].get_msb();
			ret.push_back(netrange_t(tmp, tmp));
		}
	}

	ret.push_back(netrange_t(base+wid, base));
	return;
}
/*}}}*/
/* eval in for loop {{{*/

/*
 * evaluate an NetExpr* under the context of current step variables.
 * */
static NetEConst*
eval_with(const NetExpr *expr, const std::map<const NetNet*, const NetEConst*>&vm)
{
	NetExpr *n_expr = copy_replace(expr, vm);
	if (NetEConst *c = dynamic_cast<typeof(c)>(n_expr)) {
		return c;
	}

	NetExpr *res = n_expr->eval_tree();
	delete n_expr;

	return dynamic_cast<NetEConst*>(res);
}

/*
 * take an NetExpr and make a copy of it which have all NetESignal inside it
 * that are also in vm replaced with its corresponding CURRENT value.
 * */
static NetExpr*
copy_replace(const NetExpr *expr,const std::map<const NetNet*, const NetEConst*>&vm)
{
	if (!expr) return 0;
	if (const NetEConst *e = dynamic_cast<const NetEConst*>(expr)) {
		NetExpr *ret = e->dup_expr();
		assert(ret->expr_width() == expr->expr_width()); // return the same size.
		return ret;
	}

	if (const NetEBinary *e = dynamic_cast<const NetEBinary*>(expr)) {
		char op = e->op();

		NetExpr *l = copy_replace(e->left(),vm);
		NetExpr *r = copy_replace(e->right(),vm);
		unsigned wid = e->expr_width();
		bool signed_flag = e->has_sign();

		switch(op) {
		case '+':
		case '-': {
			l = cast_to_width(l, wid, signed_flag, *e);
			assert(l->expr_width() == wid);

			r = cast_to_width(r, wid, signed_flag, *e);
			assert(r->expr_width() == wid);

			NetEBAdd * ret = new NetEBAdd(op, l, r, wid, signed_flag);
			assert(ret->expr_width() == wid);
			return ret;
		}
		case '/':
		case '%':
			return new NetEBDiv(op, l, r, wid, signed_flag);
		case '^':
		case '&':
		case '|':
		case 'O':
		case 'X':
			return new NetEBBits(op, l, r, wid, signed_flag);
		case '<':
		case '>':
		case 'e':
		case 'E':
		case 'L':
		case 'G':
		case 'n':
		case 'N':
			return new NetEBComp(op, l, r);
		case 'a':
		case 'o':
			return new NetEBLogic(op, l, r);
		case 'm':
		case 'M':
			return new NetEBMinMax(op, l, r, wid, signed_flag);
		case '*':
			return new NetEBMult(op, l, r, wid, signed_flag);
		case 'p':
			return new NetEBPow(op, l, r, wid, signed_flag);
		case 'l':
		case 'r':
		case 'R':
			return new NetEBShift(op, l, r, wid, signed_flag);
		default:
			ivl_assert(*expr, !"Unknown binary operator");
		}
	}
	if (const NetESelect *e = dynamic_cast<const NetESelect*>(expr)) {
		// must be constant
		NetExpr *exp = copy_replace(e->sub_expr(), vm);
		NetExpr *base = copy_replace(e->select(), vm);
		unsigned wid = e->expr_width();
		ivl_select_type_t sel_type = e->select_type();

		return new NetESelect(exp, base, wid, sel_type);
	}
	if (const NetESignal *e = dynamic_cast<const NetESignal*>(expr)) {
		if (vm.find(e->sig()) != vm.end()) {
			// const NetEConst *c = vm[e->sig()];
			const NetEConst *c = vm.find(e->sig())->second;
			if (c) {
				assert(c->expr_width() == expr->expr_width());
				return c->dup_expr();
			}
		}
		// something wrong

		return e->dup_expr();

	}
	if (const NetEUnary *e = dynamic_cast<const NetEUnary*>(expr)) {
		char op = e->op();
		NetExpr *ex = copy_replace(e->expr(), vm);
		unsigned wid = e->expr_width();
		bool signed_flag = e->has_sign();

		return new NetEUnary(op, ex, wid, signed_flag);
	}

	if (const NetETernary *e = dynamic_cast<const NetETernary*>(expr)) {
		const NetExpr *cond = e->cond_expr();
		const NetExpr *true_val = e->true_expr();
		const NetExpr *false_val = e->false_expr();
		unsigned expr_width = e->expr_width();
		bool has_sign = e->has_sign();

		return new NetETernary(copy_replace(cond, vm),
				       copy_replace(true_val, vm),
				       copy_replace(false_val, vm),
				       expr_width,
				       has_sign);
	}

	// caoncatation expression
	//
	// An operator that can be applied only to concatenations is replication, which is expressed by a concatenation
	// preceded by a non-negative, non-x and non-z constant expression, called a replication constant
	//
	// Unlike regular concatenations, expressions containing replications shall not appear on the
	// left-hand side of an assignment and shall not be connected to output or inout ports.
	if (const NetEConcat *e = dynamic_cast<typeof(e)>(expr)) {
		// ..
		const unsigned cnt = e->nparms();
		const unsigned repeat = e->repeat();
		const ivl_variable_type_t vt = e->expr_type();
		NetEConcat *ret = new NetEConcat(cnt, repeat, vt);
		for (unsigned i = 0; i < cnt; i++) {
			ret->set(i, copy_replace(e->parm(i), vm));
		}
		return ret;
	}

	ivl_assert(*expr, !"Unsupported expression type");
	return expr->dup_expr();
}

static void
update_step_variable(NetAssign_ *as, char op, const NetEConst *rv)
{
	assert(rv);
	auto sig = as->sig();
	switch(op) {
	case 0: {
		auto tmp = env[sig];
		env[sig] = rv->dup_expr();
		delete tmp;
		break;
	}
	case '+': {
		const verinum ov = env[sig]->value();
		auto tmp = env[sig];
		env[sig] = new NetEConst(ov + rv->value());
		delete tmp;
		break;
	}
	case '-': {
		const verinum ov = env[sig]->value();
		auto tmp = env[sig];
		env[sig] = new NetEConst(ov - rv->value());
		delete tmp;
		break;
	}
	default:
		ivl_assert(*current_assign, !"unknow operator while updating step variable");
	}
}
/*}}}*/
/* NetForLoop {{{*/

void
NetForLoop::multi_driver_check() const
{
	ivl_assert(*this, index_->unpacked_dimensions() == 0);
	const NetEConst *init_val = eval_with(init_expr_, env);
	ivl_assert(*this, init_val != 0);

	env[index_] = init_val;

	NetEConst *retc;
	// XXX: can retc be z or x?
	while((retc = eval_with(condition_, env)) && retc->value().as_long()) {
		delete retc;
		statement_->multi_driver_check();

		step_statement_->multi_driver_check();
	}
	if (retc)
		delete retc;

	delete env[index_];
	env.erase(index_);
	return;
}

/*}}}*/
/* NetAssign_ {{{*/
static void
mdriven_assign(const NetAssign_ *as)
{
	if (as->nest()) {
		mdriven_assign(as->nest());
		return;
	}
	const NetNet* sig = as->sig();
	const NetExpr* word = as->word();
	const NetExpr* base = as->get_base();
	unsigned lwidth = as->lwidth();

	long uword = 0, ubase = 0;
	bool full_mem = false;
	if (word) {
		const NetEConst *c = eval_with(word, env);
		if (c) {
			uword = c->value().as_long();
			delete c;
		} else {
			full_mem = true;
		}
	}
	if (base) {
		const NetEConst *c = eval_with(base, env);
		if (c) {
			ubase = c->value().as_long();
			delete c;
		} else {
			ubase = 0;
			lwidth = sig->vector_width();
		}
	} else {
		ubase = 0;
	}

	netrange_t r;
	if (!full_mem)
		r = encode_range(sig, uword, ubase, lwidth);
	else
		r = encode_full_range(sig);

	all_assigns.add_assign(sig, sig->vector_width(), current_blk_id, current_scope,
			       current_assign, r.get_lsb(), r.get_msb());
}
/*}}}*/
/* NetAssignBase{{{*/
void
NetAssignBase::multi_driver_check() const
{
	if (debug_multi_driver_check)
		cout << this->get_fileline() << ": debug:";
	current_assign = this;

	if (env.find(this->lval_->sig()) == env.end()) {
		mdriven_assign(this->lval_);
	} else {
		// XXX: don't handle concatation assign to step variable
		//      also, not bit select, part select, memory word as step variable
		ivl_assert(*this, lval_->more == 0);
		ivl_assert(*this, lval_->get_base() == 0);
		ivl_assert(*this, lval_->word() == 0);
		if (const NetAssign *as = dynamic_cast<typeof(as)>(this)) {
			NetEConst *rv = eval_with(rval_, env);
			update_step_variable(this->lval_, as->assign_operator(), rv);
			delete rv;
		}
	}
	for (NetAssign_ *cur = lval_->more; cur; cur = cur->more) {
#if ASSIGN_IN_FOR_BODY
		if (env.find(cur->sig()) == env.end()) {
			mdriven_assign(cur);
		} else {
			ivl_assert(*this, !"lval assigned as part of a concatation not supported");
			if (const NetAssign *as = dynamic_cast<typeof(as)>(this)) {
				NetEConst *rv = eval_with(rval_, env);
				update_step_variable(cur, as->assign_operator(), rv);
				delete rv;
			}
		}
#else
		mdriven_assign(cur);
#endif
	}
}
/*}}}*/
/* misc expressions {{{*/
void
NetProc::multi_driver_check() const
{
	// empty
}

void
NetAlloc::multi_driver_check() const
{
	// what's alloc in verilog
}

void
NetBlock::multi_driver_check() const
{
	if(last_) {
		const NetProc*cur = last_;
		do {
			cur = cur->next_;
			cur->multi_driver_check();
		} while (cur != last_);
	}
}

void
NetCase::multi_driver_check() const
{
	for (auto it = items_.begin(); it != items_.end(); it++) {
		if (it->statement)
			it->statement->multi_driver_check();
	}
}

void
NetCondit::multi_driver_check() const
{
	if(if_) if_->multi_driver_check();
	if(else_) else_->multi_driver_check();
}

void
NetContribution::multi_driver_check() const
{
	// don't know what is this
}

void NetDisable::multi_driver_check() const
{
	// empty
}

void
NetDoWhile::multi_driver_check() const
{
	proc_->multi_driver_check();
}

void
NetEvTrig::multi_driver_check() const
{
	// don't matter
}

void
NetEvWait::multi_driver_check() const
{
	if (statement_)
		statement_->multi_driver_check();
}

void
NetForever::multi_driver_check() const
{
	statement_->multi_driver_check();
}

void
NetFree::multi_driver_check() const
{
	// what's free in verilog?
}

void
NetPDelay::multi_driver_check() const
{
	if (statement_)
		statement_->multi_driver_check();
}

void
NetRepeat::multi_driver_check() const
{
	statement_->multi_driver_check();
}

void
NetSTask::multi_driver_check() const
{
	// a call to system task
}

void
NetUTask::multi_driver_check() const
{
	// a elaborated class definition.
	//  what's class in verilog?
}

void
NetWhile::multi_driver_check() const
{
	proc_->multi_driver_check();
}
/*}}}*/
