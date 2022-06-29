import algebra.group.basic
import tactic
import group_theory.subgroup.basic
import data.set_like.basic
import chapter2.set_theory_cosets

variables {A:Type} [monoid A]


lemma one_lcoset (S:set A) : lcoset (A) (1) (S) = S := 
begin
unfold lcoset, 
ext x, 
simp, --that is too funny. But I know why this works so we will keep it :)
end

lemma rcoset_one (S:set A) : rcoset (A) (S) (1) = S := 
begin
unfold rcoset, 
ext x, 
simp, 
end

