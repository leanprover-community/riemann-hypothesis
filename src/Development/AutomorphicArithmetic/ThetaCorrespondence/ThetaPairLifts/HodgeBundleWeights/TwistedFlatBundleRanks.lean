import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantBoundedByNine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantBoundedByNineStatement

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.KeyTwDeep
theorem exists_twisted_section_root_of_depth : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (GlobalTheory.FlatTw.TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 1)) := by
  intro _ D T hT j hp _ _ hj Y e o hG _ _ Z
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0
  exact twSec_keyRoot _ _ _ _ _ _ _ _ _ hG.unf hG.xiAbs hG.geo (le_add_right hp) hg Z
end GlobalTheory.KeyTwDeep
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_section_with_deep_root : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (GlobalTheory.FlatTw.TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 1)) := by
  first | exact @_root_.GlobalTheory.KeyTwDeep.exists_twisted_section_root_of_depth | exact _root_.GlobalTheory.KeyTwDeep.exists_twisted_section_root_of_depth | (intros; apply _root_.GlobalTheory.KeyTwDeep.exists_twisted_section_root_of_depth <;> assumption)
end
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.TwistRank
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw
section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
end Gen
end GlobalTheory.TwistRank
namespace GlobalTheory.TwistRank
theorem flat_twist_rank_eq : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → (∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, Y.rkC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z = Y.rkC la Z) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ), Dom a n → Even n → Y.GoodAt (shiftG (T.Q.Dw j) a n s) → (Y.rk (shiftG (T.Q.Dw j) a n s) : ℝ) = ∑ᶠ Z, Y.rkC (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) Z := by
  intro hP D T hL j hp hq hE hj Y e o hY c₁ hF
  have hU := hY.unf
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hK : Nonempty (GlobalTheory.ShFam.KeySec Y.d.Xo₂ Y.d.c₂) := by
    obtain ⟨σ, hσ⟩ : ∃ σ, GoodEmb Y.d.c₂ σ := ⟨Y.d.c₂.F.val.toRingHom, rfl⟩
    obtain ⟨-, -, -, -, -, g, ee, F, -⟩ := hY.unf σ hσ
    exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F hpq hY.geo
  have part1 : ∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z,
      Y.rkC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z = Y.rkC la Z := by
    intro la w Z
    obtain ⟨t⟩ := exists_twSec_par hK hU hpq hF Z w
    show ((AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) 0) : ℕ) : ℝ) =
      ((AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) la 0) : ℕ) : ℝ)
    rw [GlobalTheory.FlatLine.wtOf_add', rankOn_twist t _ (AllWt.even_wtOf _ _)]
  refine ⟨part1, ?_⟩
  intro a n kc s _hdom hn hgood
  have hR := GlobalTheory.T.supLattice_rank_eq_sum_component_ranks D T.Q.H (T.Q.Dw j) _ Y.d.Xo₂ Y.d.c₂ _ Y.U (xiR D) (fun _ => D.sp.W j) Y.dict
    (shiftG (T.Q.Dw j) a n s) hU hgood
  haveI : Finite (Comp Y.d.Xo₂ Y.d.c₂) := GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.finite_comp
  letI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  show ((AllWt.rankW Y.U (shiftG (T.Q.Dw j) a n s) : ℕ) : ℝ) = _
  rw [hR]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  obtain ⟨m, hm⟩ := hn
  have hn2 : n / 2 = m := by omega
  set L := laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j) with hLdef
  have h1 : AllWt.rankOn Y.U Z (shiftG (T.Q.Dw j) a n s) = AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L (m : ℤ)) := by
    refine rankOn_congr hU Z ?_
    rw [hLdef, ← add_zero (m : ℤ), AllWt.wtOf_add, shiftG, GlobalTheory.FlatTw.exZ_add_eq, GlobalTheory.FlatTw.exZ_add_eq]
    congr 1
    have := AllWt.exOf_weightOf (Dw := T.Q.Dw j) (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)
    rw [AllWt.exOf] at this
    rw [laOf, hn2] at *
    rw [this, wtZ]
    congr 2
    omega
  have h2 : AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L (m : ℤ)) = AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L 0) := by
    have he : wtOf (T.Q.Dw j) L (m : ℤ) = wtOf (T.Q.Dw j) L 0 + wtOf (T.Q.Dw j) 0 (m : ℤ) := by
      rw [← AllWt.wtOf_add, add_zero, zero_add]
    obtain ⟨t1⟩ := _root_.GlobalTheory.T.exists_twisted_section_with_deep_root hP D T hL j hp hq hE hj Y e o hY c₁ hF Z
    obtain ⟨t, -⟩ := GlobalTheory.FlatTw.TwSec.exists_pow t1 m
    rw [he]
    exact rankOn_twist (t.copy (wtOf_zero_nat (Dw := T.Q.Dw j) m).symm) _ (AllWt.even_wtOf _ _)
  have h3 : L = (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) +
      GlobalTheory.FlatLine.parWt (T.Q.Dw j) (anchor (T.Q.Dw j) a n kc) := by
    rw [hLdef, ← uWt_add_anchor (T.Q.Dw j) a n kc]; abel
  have h4 := part1 (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) (anchor (T.Q.Dw j) a n kc) Z
  rw [← h3] at h4
  rw [h1, h2]
  exact h4
end GlobalTheory.TwistRank
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_flat_bundle_ranks : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → (∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, Y.rkC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z = Y.rkC la Z) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ), Dom a n → Even n → Y.GoodAt (shiftG (T.Q.Dw j) a n s) → (Y.rk (shiftG (T.Q.Dw j) a n s) : ℝ) = ∑ᶠ Z, Y.rkC (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) Z := by
  first | exact @_root_.GlobalTheory.TwistRank.flat_twist_rank_eq | exact _root_.GlobalTheory.TwistRank.flat_twist_rank_eq | (intros; apply _root_.GlobalTheory.TwistRank.flat_twist_rank_eq <;> assumption)
end
end
