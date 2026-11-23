module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuMor
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.OmMorPullIndep
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SchFnPtTw
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.GenMuNu
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false



noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb.Mid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem frobenius_iterate_point {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (n N : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb κ true n)).obj B₀) (h : (l : B₀) = 0) :
    ((IterG.PtN (B.phiPt F κ n) N).app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom (frbN h N)) y.1.2 := by
  induction N with
  | zero =>
    change y.1.2 = F.Pt.map (CommRingCat.ofHom (RingHom.id _)) y.1.2
    rw [CommRingCat.ofHom_id, F.Pt.map_id]
    rfl
  | succ N ih =>
    change F.Pt.map (CommRingCat.ofHom (B.frb h)) ((IterG.PtN (B.phiPt F κ n) N).app B₀ y).1.2 = _
    rw [ih]
    have e : CommRingCat.ofHom (frbN h (N + 1)) = CommRingCat.ofHom (frbN h N) ≫ CommRingCat.ofHom (B.frb h) :=
      CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
    rw [e, F.Pt.map_comp]
    rfl

theorem frobenius_mu_nu_iterate (r : Res l K) (N : ℕ) (hT : TeichmullerCongruence r N) (M : Model l K) (n j : ℕ)
    (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    mu r M n j hT (nu r M n j hT x) = (⇑(B.phiHc (B.schFn M.p) (okToOC l K) n j))^[N] x := by
  unfold mu nu muMor nuMor mIn mOut B.phiHc B.phiMorC phiP phiA
  exact IterG.gen_mu_nu (b := B.bs l true n) (ht := rfl) (F := B.schFn M.p) (κ := B.κb (okToOC l K) true n) (κ' := κm r n)
    ((base l).cris n) _ (B.phiPt (B.schFn M.p) (okToOC l K) n) _ _ N _ (ptIn (B.schFn M.p) n hT) _ _ _ (ptOut (B.schFn M.p) n hT) _ _
    (fun B₀ y => (frobenius_iterate_point (B.schFn M.p) (okToOC l K) n N B₀ y (l_zero y.1.1)).symm) j x

end CrystallineSemistableComparison.Pb.Mid
