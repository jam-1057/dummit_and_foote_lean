import algebra.group.basic
import tactic
import group_theory.subgroup.basic
import data.set_like.basic
import chapter2.set_theory_cosets
import chapter2.set_theory_cosets_continued_w_semigroups
import chapter2.set_theory_cosets_continued_w_monoids
import chapter2.set_theory_cosets_continued_w_groups

variables {A:Type} [group A] {G:subgroup A}

lemma lcoset_eq_self_of_mem {a:A} (Ha: a ∈ G) : lcoset (A) (a) (G) = G :=
begin
unfold lcoset, ext x, split,
{intro hx, cases hx with x2 hx2, dsimp at hx2, cases hx2 with hx3 hx4, 
have hx5 : a*x2 ∈ G, 
exact G.mul_mem Ha hx3, rw hx4 at hx5, exact hx5,},
{intro hx, simp, 
have h2 : a⁻¹ ∈ G, 
exact G.inv_mem Ha, 
have h3 : a⁻¹ * x ∈ G,
exact G.mul_mem h2 hx, exact h3,}
end

--cool because it requires the subgroup to be closed under multiplication which is obviously part of the subgroups definition. 

lemma rcoset_eq_self_of_mem {a:A} (Ha: a ∈ G) : rcoset (A) (G) (a) = G :=
begin
unfold rcoset, ext x, split, 
{intro hx, simp at hx, 
have h2: x*a⁻¹*a ∈ G, exact G.mul_mem hx Ha,
simp at h2, exact h2,},
{intro hx, simp, 
have h2: a⁻¹ ∈ G, exact G.inv_mem Ha,
have h3: x* a⁻¹ ∈ G, exact G.mul_mem hx h2, exact h3,} 
end

lemma mem_lcoset_self (a:A) : a ∈ lcoset (A) (a) (G) :=
begin
unfold lcoset, use 1, split, 
{simp, exact G.one_mem, },
{simp, } 
end

lemma mem_rcoset_self (a:A) : a ∈ rcoset (A) (G) (a) :=
begin
unfold rcoset, use 1, split, 
{simp, exact G.one_mem, },
{simp, }
end

lemma lcoset_eq_self_iff {a:A} : lcoset (A) (a) (G) = G ↔ a ∈ G := 
begin
unfold lcoset, split, 
{intro h, have h2 : a ∈ lcoset (A) (a) (G), exact mem_lcoset_self a, unfold lcoset at h2,
rw h at h2, exact h2,},
{intro h, exact lcoset_eq_self_of_mem h,}
end

lemma rcoset_eq_self_iff {a:A} : rcoset (A) (G) (a) = G ↔ a ∈ G :=
begin
split, 
{intro h, have h2 : a ∈ rcoset (A) (G) (a), exact mem_rcoset_self a, rw h at h2, exact h2,},
{intro h, exact rcoset_eq_self_of_mem h,} 
end

lemma lcoset_eq_lcoset (a b : A) (Hab : b⁻¹ * a ∈ G) : lcoset (A) (b) (G) = lcoset (A) (a) (G) := 
begin
have h1: lcoset (A) (b⁻¹ * a) (G) = G, exact lcoset_eq_self_of_mem Hab,  
have h2: lcoset (A) (1) (G) = G, exact one_lcoset (G),
have h3: b⁻¹*b = 1, exact inv_mul_self b,
rw ← h3 at h2,  
nth_rewrite 1 ← h1 at h2, 
rw ← lcoset_lcoset at h2,
rw ← lcoset_lcoset at h2, 
exact eq_of_lcoset_eq_lcoset _ _ _ h2, -- was feeling a bit lazy ;)
end

lemma inv_mul_mem_of_lcoset_eq_lcoset (a b : A) (Hab : lcoset (A) (b) (G) = lcoset (A) (a) (G)) : b⁻¹ * a ∈ G := 
begin
have h : lcoset (A) (1) (G) = G, 
exact one_lcoset (G), 
have h2 : b⁻¹*b = 1, 
exact inv_mul_self b,
rw ← h2 at h,
rw ← lcoset_lcoset at h,
rw Hab at h,
rw lcoset_lcoset at h,
rw lcoset_eq_self_iff at h,
exact h,
end

lemma lcoset_eq_lcoset_iff (a b : A) : lcoset (A) (b) (G) = lcoset (A) (a) (G) ↔ b⁻¹*a ∈ G := 
begin
split, 
{intro h, exact inv_mul_mem_of_lcoset_eq_lcoset a b h,},
{intro h, exact lcoset_eq_lcoset a b h,}
end

lemma rcoset_eq_rcoset {a b : A} (Hab : a * b⁻¹ ∈ G) : rcoset (A) (G) (a) = rcoset (A) (G) (b) :=
begin
have h : rcoset (A) (G) (a*b⁻¹) = G,
exact rcoset_eq_self_of_mem Hab,
have h2 : rcoset (A) (G) (1) = G, 
exact rcoset_one (G), 
have h3: b*b⁻¹ = 1, 
exact mul_inv_self b,
rw ← h3 at h2,
nth_rewrite 1 ← h2 at h,
rw ← rcoset_rcoset at h,
rw ← rcoset_rcoset at h,
exact eq_of_rcoset_eq_rcoset _ _ _ h,
end

lemma mul_inv_mem_of_rcoset_eq_rcoset {a b : A} (H : rcoset (A) (G) (a) = rcoset (A) (G) (b)) : a * b⁻¹ ∈ G :=
begin
have h : rcoset (A) (G) (1) = G, 
exact rcoset_one (G), 
have h2 : b*b⁻¹ = 1, 
exact mul_inv_self b,
rw ← h2 at h,
rw ← rcoset_rcoset at h,
rw ← H at h,
rw rcoset_rcoset at h,
rw rcoset_eq_self_iff at h,
exact h,
end

lemma rcoset_eq_lcoset_iff (a b : A) : rcoset (A) (G) (a) = rcoset (A) (G) (b) ↔ a*b⁻¹ ∈ G :=
begin 
split, 
{intro h, exact mul_inv_mem_of_rcoset_eq_rcoset h,},
{intro h, exact rcoset_eq_rcoset h,}
end
