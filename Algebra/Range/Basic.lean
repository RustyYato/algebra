import Algebra.Nat.Mul

structure range (min max: nat) where
  value: nat
  min_le_value: min ≤ value
  value_lt_max: value < max

def range.empty : range a a -> False := by
  intro r
  apply not_lt_of_ge r.value_lt_max
  exact r.min_le_value

def range.for_value (value: nat) : range value value.succ := by
  apply range.mk value
  apply le_refl
  apply nat.lt_succ_self

def range.reduce_min { min max: nat } (r: range min max) (min': nat) : min' ≤ min -> range min' max := by
  intro min'_le
  apply range.mk r.value
  exact le_trans min'_le r.min_le_value
  exact r.value_lt_max

def range.increase_max { min max: nat } (r: range min max) (max': nat) : max ≤ max' -> range min max' := by
  intro max'_le
  apply range.mk r.value
  exact r.min_le_value
  exact lt_of_lt_of_le r.value_lt_max max'_le

def range.try_update_min { min max: nat } (r: range min max) (min': nat) :
  Option (range min' max) :=
  if h:min' ≤ r.value then by
    apply Option.some (range.mk r.value h r.value_lt_max)
  else
    .none

def range.try_update_max { min max: nat } (r: range min max) (max': nat) :
  Option (range min max') :=
  if h:r.value < max' then by
    apply Option.some (range.mk r.value r.min_le_value h)
  else
    .none

def range.add (a: range mina maxa) (b: range minb maxb) : range (mina + minb) (maxa + maxb) := by
  apply range.mk (a.value + b.value)
  apply nat.add.le
  exact a.min_le_value
  exact b.min_le_value
  apply nat.add.lt
  exact a.value_lt_max
  exact b.value_lt_max

def range.mul (a: range mina maxa) (b: range minb maxb) : range (mina * minb) (maxa * maxb) := by
  apply range.mk (a.value * b.value)
  apply nat.mul.le
  exact a.min_le_value
  exact b.min_le_value
  apply nat.mul.lt
  exact a.value_lt_max
  exact b.value_lt_max
