/-
Author: Justin Mayer
self study of abstract algebra. Chapter two of dummit and foote. 
-/

import tactic
import algebra.group.basic
import group_theory.subgroup.basic
import data.set.basic

--#print subgroup

variables {G: Type} [group G] (H : subgroup G)

instance : has_mem G (subgroup G) := 
{mem := λ m H, m ∈ H.carrier } --this allows for g ∈ H to be written. See formalising math by Kevin Buzzard. Groups, sheet 3

instance : has_coe (subgroup G) (set G) := 
{coe := λ H, H.carrier} --just removing the need to reference H.carrier since this doesn't feel very "mathy." Once again a trick demonstrated by Kevin Buzzard. Formalising mathematics, Groups, sheet 3. 
--notice that these are instances of general functions definied in lean. We then define the mem function using the lambda calculus formalism. 

@[simp] lemma mem_coe {g:G} : g ∈ (H : set G) ↔ g ∈ H := 
begin 
refl,
end
--always for a rewrite where if something has type g ∈ (H : set G), then it can just be written as g ∈ H. Another useful math tactic.

@[ext] def ext' (H K : subgroup G) (h : ∀ g : G, g ∈ H ↔ g ∈ K) : H = K :=
begin
ext x,
exact h x,
end
--another extensionality theorem that asserts two subgroups are equal iff every element is contained in both subgroups. 

--finally, remove all refereneces to the carrier function:

theorem one_mem : (1:G) ∈ H :=
begin
apply H.one_mem',
end

theorem mul_mem {x y : G}: x ∈ H → y ∈ H → x*y ∈ H :=
begin
apply H.mul_mem',
end

theorem inv_mem {x:G} : x ∈ H → x⁻¹ ∈ H := 
begin
apply H.inv_mem',
end

--A subgroup has now been defined in a way that is natural to the notation in dummit foote. The three important theorems to use are: 
-- H.one_mem :  (1:G) ∈ H
-- H.mul_mem :  x ∈ H → y ∈ H → x * y ∈ H
-- H.inv_mem : x ∈ H → x⁻¹ ∈ H

--the subgroup criterion mentioned on page 46
lemma subgroup_crit {G : Type} [group G] (H : subgroup G) : (∃ g : G, g ∈ H)  ∧ ∀ x y : G, x ∈ H → y ∈ H → x*y⁻¹ ∈ H := 
begin
split,
have h: (1:G) ∈ H := H.one_mem,
use (1:G),
exact h,
intros x y hx hy,
have h2: y⁻¹ ∈ H := H.inv_mem hy,
exact H.mul_mem hx h2,
end

--define a structure mysubgroup based on the fact that it is a nonempty subset of G with a particular multiplication relation on the subset.
--does this structure end up being a subgroup? Let's find out!

structure mysubgroup (G:Type) [group G] := 
(carrier : set G)
(non_empty' : carrier.nonempty)
(mul_con' : ∀ x y: G, x ∈ carrier → y ∈ carrier → x*y⁻¹ ∈ carrier)

variables (P : mysubgroup G)

instance : has_mem G (mysubgroup G) := 
{mem := λ m P, m ∈ P.carrier } 

--#print mysubgroup 
lemma mysubgroup_one_mem (P:mysubgroup G) : (1:G) ∈ P.carrier :=
begin
have h: ∃ x:G, x ∈ P.carrier := P.non_empty',
cases h with x hx,
have h2: x*x⁻¹ ∈ P.carrier := P.mul_con' x x hx hx,
simp at h2,
exact h2,
end

lemma mysubgroup_inv_mem (P:mysubgroup G) : ∀ x:G, x∈P.carrier → x⁻¹∈P.carrier :=
begin
intros x hx,
have h1: (1:G) ∈ P.carrier := mysubgroup_one_mem P,
have h2: 1*x⁻¹ ∈ P.carrier := P.mul_con' (1:G) x h1 hx,
simp at h2,
exact h2, 
end

lemma mysubgroup_mul_mem (P:mysubgroup G) : ∀ x y : G, x∈P.carrier → y∈P.carrier → x*y ∈ P.carrier :=
begin
intros x y hx hy,
have h1: y⁻¹ ∈ P.carrier := mysubgroup_inv_mem P y hy,
have h2: x*y⁻¹⁻¹ ∈ P.carrier := P.mul_con' x y⁻¹ hx h1,
simp at h2,
exact h2,
end

--based on these three lemmas the definition mysubgroup is clearly a group! I think to be completely precise
--it may also make sense to show that mysubgroup is an instance of subgroup. Do this with Harlan perhaps?



