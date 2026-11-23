module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
variable {l : ℕ} {x δ : kˣ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
  {P T : Matrix (Fin n) (Fin n) ℂ}
end Loc
def LocDataTAlt : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ x δ : (w.adicCompletion E)ˣ, IsUnif x ∧ IsGenMod _ (ellC l _) δ ∧ ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), (∀ rc : IrrGL (k := w.adicCompletion E) → WD hB, IsRecT hB rc → WDT ι r (rc (algNorm σ))) → LocRelT l x δ σ.ρ ((r fr : Matrix (Fin n) (Fin n) (Qbar l)).map ι) ((r τ : Matrix (Fin n) (Fin n) (Qbar l)).map ι)
end UpperTheory.V.Z.Win
end
end
