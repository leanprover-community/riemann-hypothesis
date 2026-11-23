module

public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable (F) in
def vi (x : n → E) : n → 𝒜 := fun i => ιA (x i)

theorem vi_mem_hat {Λ : Submodule (𝓞 E) (n → E)} {x : n → E} (hx : x ∈ Λ) : vi F x ∈ hat F Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem gmv (G : Matrix n n E) (x : n → E) : (G.map ιA) *ᵥ vi F x = vi F (G *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec ιA G x i).symm

theorem hat_fwd (G : Matrix n n E) {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x ∈ Λ, G *ᵥ x ∈ Λ')
    (u : n → 𝒜) (hu : u ∈ hat F Λ) : (G.map ιA) *ᵥ u ∈ hat F Λ' := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    show G.map ιA *ᵥ vi F x ∈ _
    rw [gmv]
    exact vi_mem_hat (h x hx)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mulVec_add]; exact add_mem hu hw
  | smul s u _ hu =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ s hu

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
