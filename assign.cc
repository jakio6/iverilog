#include "assign.h"

#include <assert.h>
#include <cstdio>
#include <iterator>
#include <list>

std::list<assign::range_t>
merge_recursive(info_store &store,
		std::list<assign::range_t> &ranges,
		std::list<assign::range_t>::iterator it_start,
		std::list<assign::range_t>::iterator it_end
	       )
{
	int len = std::distance(it_start, it_end);
	std::list<assign::range_t> ret;
	if (len == 0) {
		return ret;
	}

	if (len == 1) {
		// ret.push_back(*it_start);
		ret.splice(ret.end(), ranges, it_start);
		return ret;
	}

	auto mid = it_start;
	advance(mid, len / 2);
	std::list<assign::range_t> l = merge_recursive(store, ranges, it_start, mid);
	std::list<assign::range_t> r = merge_recursive(store, ranges, mid, it_end);

	// merge
	auto itl = l.begin();
	auto itr = r.begin();
	for (;itl != l.end() && itr != r.end();) {
		auto it = &itl;
		auto ito = &itr;
		auto lp = &l;
		auto lpo = &r;
		if ((*it)->start_offset < (*ito)->start_offset) {
			std::swap(it, ito);
			std::swap(lp, lpo);
		}
		assert((*it)->start_offset >= (*ito)->start_offset);

		// non overlapping case
		if ((*it)->start_offset > (*ito)->end_offset) {
			// don't copy, splice
			ret.splice(ret.end(), *lpo, (*ito)++);
			continue;
		}

		// overlapping case, split a new range
		auto tmp = **ito;

		// it :      ____________
		// ito: ___________
		if ((*it)->start_offset > (*ito)->start_offset) {
			tmp.end_offset = (*it)->start_offset - 1;
			ret.push_back(tmp);

			(*ito)->start_offset = (*it)->start_offset;
		}

		// _____   , ________ , ______
		// _______ , _____    , ______
		if ((*it)->end_offset > (*ito)->end_offset) {
			std::swap(it, ito);
			std::swap(lp, lpo);
		}

		assert((*it)->end_offset <= (*ito)->end_offset);

		// _____   , ______
		// _______ , ______
		// overlapped part, merge
		(*it)->assignments = store.key_merge((*it)->assignments, (*ito)->assignments);
		(*it)->conflict_on_this_p |= (*ito)->conflict_on_this_p;
		(*it)->conflict_on_this_p |= (*ito)->last_blk_id != (*it)->last_blk_id;

		// try dop ito
		if ((*ito)->end_offset == (*it)->end_offset) {
			(*lpo).erase((*ito)++);
		} else {
			(*ito)->start_offset = (*it)->end_offset + 1;
		}

		// it : _____   , _____
		// ito:      __ ,

		// splice it
		ret.splice(ret.end(), *lp, (*it)++);
	}
	assert(l.empty() || r.empty());
	ret.splice(ret.end(), l);
	ret.splice(ret.end(), r);

	return ret;
}

void assign::merge(info_store &store)
{
	std::list<range_t> nv;

	std::list<range_t> mem_assign_alls;
	for (auto it = ranges_.begin(); it != ranges_.end();) {
		if (it->end_offset - it->start_offset > sig_wid) {
			mem_assign_alls.splice(mem_assign_alls.end(),
					       ranges_, it++);
		} else {
			it++;
		}
	}

	if (!mem_assign_alls.empty()) {
		std::list<range_t> x = merge_recursive(store,
						       mem_assign_alls,
						       mem_assign_alls.begin(),
						       mem_assign_alls.end());
		assert(x.size() == 1);
		auto tmp = x.front();
		if (tmp.conflict_on_this_p) {
			nv.push_back(tmp);
		}

		tmp.conflict_on_this_p = 0;
		tmp.last_blk_id = -1;
		ranges_.push_back(tmp);
	}

	std::list<range_t> v = merge_recursive(store, ranges_, ranges_.begin(),
					       ranges_.end());

	assert(ranges_.empty());

	ranges_.splice(ranges_.end(), nv);
	ranges_.splice(ranges_.end(), v);
	return;
}

void proc::merge()
{
	for (auto it = assigns_.begin();
	     it != assigns_.end();
	     it++) {
		it->second.merge(store);
	}
}

void proc::report_conflict()
{
	if (!conflict_cb_) return;
	for (auto const &as : assigns_) {
		for (auto const &r : as.second.ranges()) {
			if (r.conflict_on_this_p) {
				conflict_cb_(as.first,
					     store.key_get(r.assignments),
					     r.start_offset,
					     r.end_offset);
			}
		}
	}
}
