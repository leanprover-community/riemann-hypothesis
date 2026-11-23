module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.Forms
open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem AdFun_transport (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (g) (hg : g ∈ AdFun S emb) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x'.1 = x.1 * κ.1)
    (y y' : Frames (gramC J emb)) (hy : IsTr (atInf emb γ) y' y) :
    g x y = ((S.chi κ)⁻¹ : ℂˣ) * g x' y' := by
  have h2 : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x'.1 * (κ⁻¹ : S.U).1 := by
    rw [h]; simp
  have := hg γ hγ x' x κ⁻¹ h2 y y' hy
  rw [this, map_inv]

end Formalism.L2.Forms
