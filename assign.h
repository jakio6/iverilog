#pragma once
#include "netlist.h"
#include <algorithm>
#include <utility>
#include <vector>
#include <list>
#include <map>
#include <set>
#include <iostream>
#include <assert.h>

#define ASSIGN_IN_FOR_BODY 0

typedef std::pair<const void *, const void*> assign_info_t;

class info_store;
/*
 * 用于记录对一个reg的全部赋值信息
 * */
class assign {
public:
	typedef struct range_s {
		bool conflict_on_this_p;
		long start_offset;
		long end_offset;
		int last_blk_id;
		int assignments;

		range_s (): conflict_on_this_p(false), start_offset(0),
				end_offset(0), last_blk_id(0), assignments(0){}

		range_s (long so, long eo, bool cp = false, int li = 0,
			 int as = 0)
			: conflict_on_this_p(cp), start_offset(so), end_offset(eo), last_blk_id(li), assignments(as) {}
	} range_t;

public:
	assign(){}
	const std::list<range_t> &ranges() const { return ranges_; }
	void add_range(long so, long eo, bool cp, int li,
		       int assignments)
	{
		ranges_.push_back(range_s(so, eo, cp, li, assignments));
	}
	void merge(info_store &store);
	void set_sig_wid(unsigned w) {sig_wid = w;};

private:
	std::list<range_t> ranges_; // 我就先不用range了.
	unsigned sig_wid;
};

/*
 * keep every uniq set uniq, to save storage.
 * */
class info_store {
	std::map<int, const std::set<assign_info_t>> key_to_info;
	std::map<const void *, int> as_base_to_key;
	std::map<const std::pair<int, int>, int> key2_to_key;
	std::map<const std::set<assign_info_t>, int> info_to_key;
	int max_key = 0;
public:
	int key_new(const std::set<assign_info_t>& x) {
		if (info_to_key.find(x) != info_to_key.end())
			return info_to_key.find(x)->second;

		int new_key = max_key++;
		key_to_info.insert(std::make_pair(new_key, x));
		info_to_key.insert(std::make_pair(x, new_key));
		return new_key;
	}

	int key_merge(int k1, int k2) {
		if (k1 > k2) {
			std::swap(k1, k2);
		}
		std::pair<int,int> kp = std::make_pair(k1,k2);
		auto it = key2_to_key.find(kp);
		if (it != key2_to_key.end())
			return it->second;

		auto const &info1 = key_to_info[k1];
		auto const &info2 = key_to_info[k2];

		auto info3 = info1;
		info3.insert(info2.begin(), info2.end());
		int k3 = key_new(info3);
		key2_to_key.insert(std::make_pair(kp, k3));

		return k3;
	}

	const std::set<assign_info_t> &key_get(int key) const {
		return key_to_info.find(key)->second;
	}

	int base_to_key(const void *scope, const void *where) {
		if (as_base_to_key.find(where) != as_base_to_key.end())
			return as_base_to_key[where];
		assign_info_t info = std::make_pair(scope, where);
		std::set<assign_info_t> infos;
		infos.insert(info);

		int k = key_new(infos);
		as_base_to_key[where] = key_new(infos);

		return k;
	}
};

/*
 * 表示一个block的数据结构.
 *  这个结构由assign构成.
 * */
class proc {
	// signal to assign map
	std::map<const void *, assign> assigns_;
	typedef int (*conflict_cb_t) (const void *, const std::set<assign_info_t> &,
				      long start,
				      long end);
	info_store store;
	conflict_cb_t conflict_cb_ = 0;
public:
	proc () {}
	proc (conflict_cb_t cb): conflict_cb_(cb){}
	void set_cb(conflict_cb_t cb) { conflict_cb_ = cb; }

	void add_assign(const void *sig, unsigned sig_wid, int blk_id, const void *scope, const void *where, long ubase, long uend)
	{
		const void *key = sig;
		if (assigns_.find(key) == assigns_.end()) {
			assigns_[key] = assign();
			assigns_[key].set_sig_wid(sig_wid);
		}

		assigns_[key].add_range(ubase, uend, false, blk_id,
					store.base_to_key(scope, where));
	}

	void merge();
	void report_conflict();
};
