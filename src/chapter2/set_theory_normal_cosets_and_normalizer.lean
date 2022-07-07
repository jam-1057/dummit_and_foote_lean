import algebra.group.basic
import tactic
import group_theory.subgroup.basic
import data.set_like.basic
import chapter2.set_theory_cosets

variables {A:Type} [has_mul A]

definition normalizes (a:A) (S:set A) : Prop := lcoset (A) (a) (S) = rcoset (A) (S) (a)

definition is_normal (S: set A) : Prop := ∀a, normalizes a S

definition normalizer (S : set A) : set A := { a : A | normalizes a S} --this definition will also work for subgroups! 

definition is_normal_in (S T : set A) : Prop := T ⊆ normalizer S

lemma lcoset_eq_rcoset (a : A) (S : set A) (H : is_normal S) : lcoset (A) (a) (S) = rcoset (A) (S) (a) :=
begin
unfold is_normal at H, specialize H a, exact H,
end --this helps get a feel for these new definitions. 

lemma lcoset_eq_rcoset_of_mem {a:A} (S:set A) {T:set A} (H : is_normal_in S T) (amemT : a ∈ T) : lcoset (A) (a) (S) = rcoset (A) (S) (a) :=
begin
unfold is_normal_in at H, specialize H amemT, exact H, --was curious if lean would understand this.
end




