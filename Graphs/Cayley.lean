import Mathlib

variable {G : Type*} [Group G]

namespace Group

structure GenSet (G : Type*) [Group G] where
  els : Finset G
  sym {s : G} (hs : s ∈ els) : s⁻¹ ∈ els
  gen : Subgroup.closure (els : Set G) = ⊤
  nem : els.Nonempty
  irr : 1 ∉ els

instance : Membership G (GenSet G) := ⟨fun s a => a ∈ s.els⟩

variable {S : GenSet G} {x y a b : G}

namespace GenSet

def Adj (S : GenSet G) (x y : G) : Prop := x⁻¹ * y ∈ S.els

@[simp] theorem Adj.mul_left (h : S.Adj x y) (a : G) : S.Adj (a * x) (a * y) := by
  simp only [Adj] at h ⊢ ; group at h ⊢ ; assumption

@[symm] theorem Adj.symm (h : S.Adj x y) : S.Adj y x := by
  simpa [Adj] using S.sym h

end GenSet

end Group

variable {S : Group.GenSet G}

namespace SimpleGraph

def CayleyGraph (S : Group.GenSet G) : SimpleGraph G where
  Adj := S.Adj
  symm x y h := h.symm
  loopless x h := S.irr (by simpa [Group.GenSet.Adj] using h)

namespace CayleyGraph

def mul_left (a : G) : CayleyGraph S →g CayleyGraph S where
  toFun x := a * x
  map_rel' h := h.mul_left a

-- lemma shift : reachable (Cay S) x y → reachable (Cay S) (a*x) (a*y) :=
-- nonempty.map (walk.map (left_shift a))

-- lemma inv {h : reachable (Cay S) 1 x} : reachable (Cay S) 1 x⁻¹ :=
-- by { symmetry, convert @shift _ _ _ x⁻¹ _ _ h; group }

-- lemma reachable_mp : reachable (Cay S) 1 x :=
-- begin
--   apply subgroup.closure_induction,
--   { rw S.gen, trivial },
--   { intros y h, apply reachable.step, simpa only [Cay,genset.adj,one_inv,one_mul] },
--   { refl },
--   { intros u v h1 h2, refine reachable.trans h1 _, convert shift h2, group },
--   { intros y h, apply inv, exact h }
-- end

-- theorem Cay.connected : connected (Cay S) :=
-- ⟨λ x y, reachable_mp.symm.trans reachable_mp, ⟨1⟩⟩

-- lemma covariant : (Cay S).dist (a*x) (a*y) = (Cay S).dist x y :=
-- begin
--   have lem : ∀ a {x y}, (Cay S).dist (a*x) (a*y) ≤ (Cay S).dist x y :=
--   by { intros a x y, obtain ⟨p,hp⟩ := Cay.connected.exists_walk_of_dist x y,
--     rw [←hp,←walk.length_map], exact dist_le (p.map (left_shift a)) },
--   apply le_antisymm (lem a), convert lem a⁻¹, group
-- end

-- noncomputable def distorsion (S1 S2 : genset G) :=
-- classical.some (finset.max_of_nonempty (S1.nem.image ((Cay S2).dist 1)))

-- lemma distorsion_spec : distorsion S1 S2 ∈ (finset.image ((Cay S2).dist 1) S1.els).max :=
-- classical.some_spec (finset.max_of_nonempty (S1.nem.image ((Cay S2).dist 1)))

-- lemma distorsion_le {h : (Cay S1).adj x y} : (Cay S2).dist x y ≤ distorsion S1 S2 :=
-- begin
--   refine finset.le_max_of_mem _ distorsion_spec,
--   rw [finset.mem_image], refine ⟨x⁻¹ * y, h, _⟩, convert covariant, group
-- end

-- lemma lipschitz : (Cay S2).dist x y <= (distorsion S1 S2) * (Cay S1).dist x y :=
-- begin
--   obtain ⟨p,hp⟩ := (@Cay.connected _ _ S1).exists_walk_of_dist x y, rw <-hp, clear hp,
--   induction p with u u v w h p ih,
--   { simp only [dist_self, walk.length_nil, mul_zero] },
--   { simp only [walk.length_cons], transitivity (Cay S2).dist u v + (Cay S2).dist v w,
--     apply Cay.connected.dist_triangle, rw [mul_add,mul_one,add_comm],
--     apply add_le_add ih, apply distorsion_le, exact h }
-- end

end CayleyGraph

end SimpleGraph
