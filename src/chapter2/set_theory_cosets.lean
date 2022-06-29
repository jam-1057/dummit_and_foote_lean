import algebra.group.basic
import tactic 
import group_theory.subgroup.basic
import data.set.basic
import data.set_like.basic
import chapter2.sheet1_subgroup_defs_and_exs

-- These next few sheets are going to be based off of Zipperer ms thesis. I want a clean definition for the centralizer and normalizer that is general 

--start with defining what is needed for the type A to only be a set with the multiplication operation. 

variables (A:Type) (B:Type) [has_mul A] [has_mul B]

definition lcoset [has_mul A] (a:A) (S: set A) : set A := (λ (x : A), a*x) '' S --the '' is very neat notation that I found in the mathlib documentation!

definition rcoset [has_mul A] (S: set A) (a:A) : set A := (λ (x:A), x*a) '' S --can I think of '' as a map function? 

--notation a ` ** ` N := lcoset (A:Type) (a:A) (N:set A)  --can't seem to get this to work

lemma mul_mem_lcoset {S : set A} {x : A} (a : A) (xS : x ∈ S) : (a*x ∈ (lcoset (A) (a) (S))) :=
begin
exact set.mem_image_of_mem (λ (x:A), a*x) xS, --ooh that is cool! I understand what is happening here. 
end 

lemma mul_mem_rcoset {S: set A} {x:A} (a:A) (xS : x ∈ S) : (x*a ∈ (rcoset (A) (S) (a))) := 
begin
exact set.mem_image_of_mem (λ (x:A), x*a) xS, 
end 

-- the following proofs allow for the idea of two left cosets being equivalent to be expressed

definition lcoset_equiv (S: set A) (a b : A) : Prop := ((lcoset (A) (a) (S)) = (lcoset (A) (b) (S)))

lemma equivalence_lcoset_reflexive (S : set A) : reflexive (lcoset_equiv (A) (S) ) := 
begin
unfold reflexive, intro x, unfold lcoset_equiv,
end

lemma equivalence_lcoset_symmetric (S : set A): symmetric (lcoset_equiv (A) (S) ) := 
begin
unfold symmetric, intros x y hxy, unfold lcoset_equiv at hxy, unfold lcoset_equiv,
rw hxy, 
end

lemma equivalence_lcoset_transitive (S: set A) : transitive (lcoset_equiv (A) (S)) := 
begin 
unfold transitive, intros x y z hxy hyz, unfold lcoset_equiv at hxy hyz ⊢, rw hxy, rw hyz,
end

lemma equivalence_lcoset_equiv (S : set A) : equivalence (lcoset_equiv (A) (S)) := --currying lcoset_equiv here so it has the type needed for an equivalence relation
mk_equivalence (lcoset_equiv (A) (S)) (equivalence_lcoset_reflexive (A) (S : set A)) (equivalence_lcoset_symmetric (A) (S : set A)) (equivalence_lcoset_transitive (A) (S: set A))

--end of lcoset_equivalence proof. 

lemma lcoset_subset_lcoset {S T : set A} (a : A) (h : T ⊆ S) : (lcoset (A) (a) (T) ⊆ lcoset (A) (a) (S)) := 
set.image_subset (λ(x:A), a*x) h 

lemma rcoset_subset_rcoset {S T : set A} (a: A) (h: T⊆S) : (rcoset (A) (T) (a) ⊆ rcoset (A) (S) (a)) :=
set.image_subset (λ(x:A), x*a) h 

--I'm a bit confused with the defnition of a homormorphism in lean. It seems to only accept monoids and groups? Although it appears to work on magamas in the context of category theory?? So following Buzzard I define a homomorphism over sets here. 
@[ext] structure magma_hom (A B: Type) [has_mul A] [has_mul B] := 
(to_fun : A → B)
(map_mul' (a b : A) : to_fun (a * b) =  to_fun a * to_fun b)

notation A ` →** ` B := magma_hom A B

instance : has_coe_to_fun (A →** B) (λ _, A → B) := 
{coe := magma_hom.to_fun}
--end of "magma" homomorphism definition

lemma image_of_lcoset_is_hom {B:Type} [has_mul B] {f : A →** B} {S:set A} {a:A} : (f '' (lcoset (A) (a) (S)) = lcoset (B) (f a) ( f '' S)) := 
begin 
unfold lcoset,
ext y, 
dsimp, split,
{intro hy,
simp at hy,
simp, 
cases hy with b hb_1, 
cases hb_1 with hb_1 hb_2,
use b, 
split, 
exact hb_1,
rw ← hb_2,
exact (f.map_mul' a b).symm,},
intro hz, 
simp at hz, 
simp,
cases hz with b hb_1,
cases hb_1 with hb_1 hb_2,
use b, 
split, 
exact hb_1, 
rw ← hb_2, 
exact f.map_mul' a b, 
end --Actually a really satisfying proof. I was able to simplify zipper's proof here! Very cool.

lemma image_of_rcoset_is_hom {B:Type} [has_mul B] {f : A →** B} {S:set A} {a:A} : (f '' (rcoset (A) (S) (a)) = rcoset (B) ( f '' S) (f a)) := 
begin 
unfold rcoset,
ext y, 
split,
intro hy, 
simp at hy, 
simp,
cases hy with b hb_1, 
cases hb_1 with hb_1 hb_2, 
use b, 
split, 
exact hb_1, 
rw ← hb_2, 
exact (f.map_mul' b a).symm,
intro hy2, 
simp at hy2, 
simp, 
cases hy2 with b hb_1, 
cases hb_1 with hb_1 hb_2, 
use b, 
split, 
exact hb_1, 
rw ← hb_2, 
exact f.map_mul' b a, 
end