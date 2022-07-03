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
sorry 
end

lemma mem_of_mul_mem_rcoset (a b : A) (S : set A) (Hab : a * b ∈ rcoset (A) (S) (b)) : a ∈ S := 
begin
sorry
end
