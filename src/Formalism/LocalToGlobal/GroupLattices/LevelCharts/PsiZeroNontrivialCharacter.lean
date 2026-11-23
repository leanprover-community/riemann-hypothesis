module

public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteCompG
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.AtGGlob
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

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}
    {Z : Type} [CommGroup Z]

theorem awayG_le_comap (p : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    awayG σE J Uloc p ≤ (Uloc v).comap (bc (prV (E := E) v)) :=
  fun x hx => ((mem_awayG σE J Uloc p x).1 hx).2 v hv


variable (σE J Uloc) in
def lamQG (Q : Finset (HeightOneSpectrum (𝓞 F))) (lamQ : ∀ v, v ∈ Q → (Uloc v →* Z)) (p : ℕ)
    (hQ : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) : awayG σE J Uloc p →* Z :=
  prodChar Q Uloc lamQ (awayG σE J Uloc p) (fun v hv => awayG_le_comap p v (hQ v hv))

end Formalism.L2.G
