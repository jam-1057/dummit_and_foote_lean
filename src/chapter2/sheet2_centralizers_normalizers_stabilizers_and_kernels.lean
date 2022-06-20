/-
Author: Justin Mayer
self study of abstract algebra. Chapter two of dummit and foote. Section 2.2
-/

import algebra.group.basic
import tactic
import group_theory.subgroup.basic
import data.set.basic
import chapter2.sheet1_subgroup_defs_and_exs

variables {G: Type} [group G] (H : subgroup G)

--define the centralizer set and prove that it is indeed a subgroup of G. 
def centralizer (A : set G) (g : G) : subgroup G := 
{ carrier := { g : G | ∀ a ∈ A, g*a*g⁻¹ = a},
one_mem' := begin intros x hx,simp, end,

mul_mem' := begin 
intros g1 g2 h_g1 h_g2,
simp at h_g1,
simp at h_g2,
intros a1 h_a1,
specialize h_g1 a1 h_a1,
specialize h_g2 a1 h_a1,
simp,
nth_rewrite 0 ← h_g2 at h_g1,
group,
simp,
have h_inv : a1*a1⁻¹ = 1 := mul_inv_self a1,
nth_rewrite 0 ← h_g1 at h_inv,
rw ← h_inv,
group,
-- a painful number of group theory operations needed here... probably can be done easier. 
 end,

inv_mem' := 
begin intros g1 h_g1,
simp at h_g1,
intros a1 h_a1,
specialize h_g1 a1 h_a1,
nth_rewrite 0 ← h_g1,
group,
end }