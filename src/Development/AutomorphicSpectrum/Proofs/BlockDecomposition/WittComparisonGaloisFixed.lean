module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.FlatAcr
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.BWGal

theorem gal_wn {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K)
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) (x : (Wc.bs l r.k n).R) :
    galBase σ n (Mid.wn r n x) = Mid.wn r n x := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Mid.wn_mk, galBase_cris, hσ]

abbrev bWM {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Wc.L l (B.schFn M.p) r.ρ n) (Mid.Lm r M n) (Mid.wn r n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl

abbrev gM {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K)
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) :
    Mor (Mid.Lm r M n) (Mid.Lm r M n) (galBase σ n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl

theorem bW_gal : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (y : (HSW r M j).M n), galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by
  intro l _ K r M σ hσ n j y
  haveI : RingHomCompTriple r.w (ACris.galCris σ) r.w := ⟨RingHom.ext hσ⟩
  refine (pull_pull r.w (bWMor r M n) (galT' r M σ hσ n) j y).trans ?_
  exact cr_pull_eq _ _ (fun T => crHom (T := (bWM r M n).obj ((gM r M σ hσ n).obj T)) (T' := (bWM r M n).obj T)
    (RingHom.id T.B) (fun x => congrArg T.i (gal_wn r σ hσ n x)) (DPMorphism.id T.δ).isDPMorphism
    fun h => (pt_id _ h _).trans rfl) (fun _ _ => rfl) (fun _ _ => rfl) j y

end GlobalTheory.CompanionTheory.BWGal
