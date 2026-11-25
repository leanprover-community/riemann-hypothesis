module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace CrystallineSemistableComparison.Ls

variable {W : Type} [CommRing W]

def prj (l : ℕ) (K : Cx.{1} W) (n : ℕ) : Cx.Hom K (quo l K n) (RingHom.id W) where
  f i := Submodule.mkQ _
  comm i x := rfl

def qred (l : ℕ) {K L : Cx.{1} W} {c : ℕ} (f : Cx.Hom K (quo l L c) (RingHom.id W)) {b : ℕ} (h : b ≤ c) :
    Cx.Hom (quo l K b) (quo l L b) (RingHom.id W) where
  f i := Submodule.liftQ _ (((redg l L h).f i).comp (f.f i)) (by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (f.f i y)
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    rw [← hz]
    change Submodule.Quotient.mk _ = (0 : (quo l L b).X i)
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩)
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (quo l L b).d i ((redg l L h).f i (f.f i x)) = (redg l L h).f (i + 1) (f.f (i + 1) (K.d i x))
    rw [(redg l L h).comm, f.comm]

def FlatL (l c : ℕ) (K : Cx.{1} W) : Prop :=
  ∀ i, (∀ x : K.X i, ((l : W) ^ c) • x = 0) ∧ ∀ a b, a + b = c → ∀ x : K.X i, ((l : W) ^ b) • x = 0 → x ∈ lpow (W := W) l (K.X i) a

def tsys (l : ℕ) (Kt : ℕ → Cx.{1} W) (ψ : ∀ n, Cx.Hom (Kt n) (quo l (Kt (n + 1)) n) (RingHom.id W))
    (hψ : ∀ n j, Function.Bijective ((ψ n).mapH j)) (j : ℕ) : Sys.{1} W where
  M n := (Kt n).H j
  r n := (LinearEquiv.ofBijective ((ψ n).mapH j) (hψ n j)).symm.toLinearMap ∘ₗ (prj l (Kt (n + 1)) n).mapH j

end CrystallineSemistableComparison.Ls

end
