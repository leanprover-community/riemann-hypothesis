module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowFixesComplementOfIsotropic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatrixMajorants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ImaginaryMajorants

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants ImaginaryMajorants
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem majorant_realFlow_transfer {r : ℕ} (X : Data E r) (ξ : Fin r → E) (t : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hz : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom) (τ : X.Ψ)
    (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => (t τ : ℂ)) x) τ w =
      X.maj x τ (Matrix.mulVec (X.flowMat ξ τ (-(t τ : ℂ))) w) := by

  have hcol : ∀ c, Matrix.mulVec (X.flowMat ξ τ (t τ : ℂ)) (X.colP x τ c) =
      X.colP (X.flow ξ (fun τ => (t τ : ℂ)) x) τ c := by
    intro c
    unfold Data.colP
    rw [Data.col_flow]
  refine maj_transfer (hx := hx) (hy := hz) (τ := τ) (g := X.flowMat ξ τ (t τ : ℂ))
    (g' := X.flowMat ξ τ (-(t τ : ℂ))) (hgg' := fun w => flowMat_inv (hiso := hiso) (a := _) (w := w))
    (hiso := fun u v => flowMat_isom_real (hiso := hiso) (t := t τ) (u := u) (v := v))
    (H1 := ?_) (H2 := ?_) (w := w)
  · intro c
    refine ⟨fun a => if a = c then 1 else 0, ?_⟩
    rw [hcol c]
    simp [ite_smul]
  · intro a
    refine ⟨fun c => if c = a then 1 else 0, ?_⟩
    simp [ite_smul, hcol]

end ReciprocityTheory.ChartRestriction.G.FD
