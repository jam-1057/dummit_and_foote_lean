import algebra.group.basic
import tactic
import group_theory.subgroup.basic
import data.set_like.basic
import chapter2.set_theory_cosets
import chapter2.set_theory_cosets_continued_w_semigroups
import chapter2.set_theory_cosets_continued_w_monoids

variables {A:Type} [group A]

lemma inv_lcoset_lcoset (a:A) (S:set A) : lcoset (A) (a⁻¹) (lcoset (A) (a) (S)) = S :=
begin
ext x, 
unfold lcoset,
split, 
{intro hx,
 simp at hx, 
 exact hx, },
{intro hx, 
 simp, 
 exact hx,}
-- because the a⁻¹*a = 1 proof is part of the simp tactic for a Type that is an instance of a group the simp tactic is really all you need here. It makes sense. 
end

lemma lcoset_inv_lcoset (a:A) (S:set A) : lcoset (A) (a) (lcoset (A) (a⁻¹) (S)) = S :=
begin 
ext x, 
unfold lcoset, 
split, 
{intro hx, simp at hx, exact hx,},
{intro hx, simp, exact hx,}
end

lemma inv_rcoset_rcoset (a:A) (S:set A) : rcoset (A) (rcoset (A) (S) (a)) (a⁻¹) = S := 
begin
ext x, 
unfold rcoset, 
split, 
{intro hx, simp at hx, exact hx,},
{intro hx, simp, exact hx,}
end

lemma rcoset_inv_rcoset (a:A) (S:set A) : rcoset (A) (rcoset (A) (S) (a⁻¹)) (a) = S:=
begin 
ext x, 
unfold rcoset, 
split, 
{intro hx, simp at hx, exact hx,},
{intro hx, simp, exact hx,} 
end 

lemma eq_of_lcoset_eq_lcoset (a:A) (S T : set A) (hST : lcoset (A) (a) (S) = (lcoset (A) (a) (T))) : S = T :=
begin
have hS : lcoset (A) (a⁻¹) (lcoset (A) (a) (S)) = S,
exact inv_lcoset_lcoset a S,
rw hST at hS,
have hT : lcoset (A) (a⁻¹) (lcoset (A) (a) (T)) = T, 
exact inv_lcoset_lcoset a T,
rw ← hS,
rw hT,
end

lemma eq_of_rcoset_eq_rcoset (a:A) (S T : set A) (hST : rcoset (A) (S) (a) = rcoset (A) (T) (a)) : S = T :=
begin
have hS : rcoset (A) (rcoset (A) (S) (a)) (a⁻¹) = S,
exact inv_rcoset_rcoset a S,
rw hST at hS, 
have hT : rcoset (A) (rcoset (A) (T) (a)) (a⁻¹) = T, 
exact inv_rcoset_rcoset a T, 
rw hS at hT,
exact hT, 
end

lemma mem_of_mul_mem_lcoset (a b : A) (S : set A) (Hab : a*b ∈ (lcoset (A) (a) (S))) : b ∈ S :=
begin
unfold lcoset at Hab,
--the simp takes care of the fact that a*b = a*c → b = c if  a b c : G and G is an instance of a group. Try proving this for a monoid if there is skepticism.  
simp at Hab,
exact Hab, 
end

lemma mul_mem_lcoset_iff (a b : A) (S: set A) : (a*b ∈ (lcoset (A) (a) (S)) ↔ b ∈ S) := 
begin
unfold lcoset, 
split, 
{intro ha, exact mem_of_mul_mem_lcoset a b S ha,},
{intro ha, simp, exact ha,} -- could use definition of appling a function over an input that is known to be in the set that is being mapped over. Instead the group instance is used to rewrite the goal.
end

lemma mem_of_mul_mem_rcoset (a b : A) (S : set A) (Hab : a * b ∈ rcoset (A) (S) (b)) : a ∈ S := 
begin
unfold rcoset at Hab, 
simp at Hab, 
exact Hab,
end

lemma mul_mem_rcoset_iff (a b : A) (S : set A) : (a * b ∈ rcoset (A) (S) (b) ↔ a ∈ S) := 
begin 
unfold rcoset, 
split,
{intro ha, exact mem_of_mul_mem_rcoset a b S ha,},
{intro ha, simp, exact ha,}
end 

lemma mem_lcoset_of_inv_mul_mem {a b : A} {S : set A} (H: a⁻¹*b ∈ S) : b ∈ lcoset (A) (a) (S) :=
begin
unfold lcoset,
use (a⁻¹ * b), split, exact H, dsimp, --notice how this applies the lambda expression
--simp will essentially solve this entire proof for you. I'm just doing this somewhat explicitly to test my understanding.#check
simp,    
end

lemma mem_lcoset_iff {a b : A} {S : set A} : a⁻¹*b ∈ S ↔ b ∈ lcoset (A) (a) (S) :=
begin
split, 
{intro h1, exact mem_lcoset_of_inv_mul_mem h1,}, 
{intro h1, unfold lcoset at h1, cases h1 with c hc, cases hc with hc1 hc2, dsimp at hc2,
have h2 : a*a⁻¹*b = b, simp, 
rw ← h2 at hc2, rw mul_assoc at hc2, 
have h3: c = (a⁻¹*b) := mul_left_cancel hc2, rw h3 at hc1, exact hc1,} -- simp probably would have done a lot of the heavy lifting but I wanted to be explicit once. 
end

lemma mem_rcoset_of_inv_mul_mem {a b : A} {S : set A} (H: b*a⁻¹ ∈ S) : b ∈ rcoset (A) (S) (a) := 
begin
unfold rcoset, simp, exact H, --here I did not do it explicitly. Damn lean is powerful...
end

lemma mem_rcoset_iff {a b : A} {S : set A} : b*a⁻¹ ∈ S ↔ b ∈ rcoset (A) (S) (a) :=
begin
split, 
{intro h1, exact mem_rcoset_of_inv_mul_mem h1,},
{intro h1, unfold rcoset at h1, simp at h1, exact h1,} --like I said, simp will do a lot of heavy lifting!
end

lemma lcoset_eq_iff_eq_inv_lcoset {a:A} {S T : set A} : lcoset A a S = T ↔ lcoset A a⁻¹ T = S :=
begin
unfold lcoset, split, 
{intro h1, rw ← h1, ext x, simp,}, --if it is not clear do dsimp first. The group structure simplifies a⁻¹*a*x = x for x, thereofore any x is in S,
{intro h1, rw ← h1, ext x, simp,}
end

lemma rcoset_eq_iff_eq_inv_rcoset {a:A} {S T : set A} : rcoset A S a = T ↔ rcoset A T a⁻¹ = S :=
begin
unfold rcoset, split,
{intro h1, rw ← h1, ext x, simp,},
{intro h1, rw ← h1, ext x, simp,}
end

lemma lcoset_inter (a:A) (S T : subgroup A) : lcoset (A) (a) (S ∩ T) = lcoset (A) (a) (S) ∩ lcoset (A) (a) (T) :=
begin
unfold lcoset, 
ext x, split, 
{intro hx, simp at hx, simp, exact hx,},
{intro hx, simp at hx ⊢, exact hx,} -- the definition of intersection gets us pretty far here.  
end

--also convenient that lcoset can take subgroup as an input because it is ultimately a set with additionally properties
lemma rcoset_inter (a:A) (S T : subgroup A) : rcoset (A) (S ∩ T) (a) = rcoset (A) (S) (a) ∩ rcoset (A) (T) (a) :=
begin
unfold rcoset, ext x, split, 
{intro hx, simp at hx ⊢, exact hx,},
{intro hx, simp at hx ⊢, exact hx,} 
end

