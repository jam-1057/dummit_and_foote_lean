import algebra.group.basic
import tactic
import group_theory.subgroup.basic
import data.set_like.basic
import chapter2.set_theory_cosets

variables {A:Type} [semigroup A]
--if I try to use these proofs on something that is not a semigroup, what would happen? 
lemma lcoset_lcoset (S: set A) (a b : A) : lcoset (A) (b) (lcoset (A) (a) (S)) = lcoset (A) (b*a) (S) := 
begin
unfold lcoset,
ext x,
simp,
split,
{intro hx, cases hx with s hs_1, cases hs_1 with hs_1 hs_2,
use s, split, exact hs_1, rw mul_assoc, exact hs_2,},
{intro hx, cases hx with s hs_1, cases hs_1 with hs_1 hs_2,
use s, split, exact hs_1, rw mul_assoc at hs_2, exact hs_2,},
end

lemma rcoset_rcoset (S: set A) (a b : A) : rcoset (A) (rcoset (A) (S) (a)) (b) = rcoset (A) (S) (a*b) := 
begin
unfold rcoset,
ext x,
simp,
split,
{intro hx, cases hx with s hs_1, cases hs_1 with hs_1 hs_2,
use s, split, exact hs_1, rw mul_assoc at hs_2, exact hs_2,},
{intro hx, cases hx with s hs_1, cases hs_1 with hs_1 hs_2,
use s, split, exact hs_1, rw mul_assoc, exact hs_2,},
end

--#print rcoset_rcoset here is my answer to the above question! It knows variable A better be an instance of a semigroup 

lemma lcoset_rcoset (S:set A) (a b : A) : rcoset (A) (lcoset (A) (a) (S)) (b) = lcoset (A) (a) (rcoset (A) (S) (b)) :=
begin
unfold lcoset, 
unfold rcoset, 
ext x, simp, 
split, 
{intro hx, cases hx with s hs_1, cases hs_1 with hs_1 hs_2,
use s, split, exact hs_1, rw mul_assoc at hs_2, exact hs_2,}, 
{intro hx, cases hx with s hs_1, cases hs_1 with hs_1 hs_2, 
use s, split, exact hs_1, rw mul_assoc, exact hs_2,},
end