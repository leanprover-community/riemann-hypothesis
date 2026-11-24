module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.DCos

section Generic

variable {R : Type} [CommRing R] {k : ℕ}

variable {E : Type} [Field E] [NumberField E]

end Generic

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ}

theorem tmul_mem {L : Set (Fin k → E)} {a : Af F} (ha : a ∈ intAf F)
    {x : Fin k → E} (hx : x ∈ L) : (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem map_mem_latHat {L L' : Set (Fin k → E)} (f : (Fin k → Af F ⊗[F] E) →+ (Fin k → Af F ⊗[F] E))
    (h : ∀ a ∈ intAf F, ∀ x ∈ L, f (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L') {u : Fin k → Af F ⊗[F] E}
    (hu : u ∈ latHat F E L) : f u ∈ latHat F E L' := by
  have : latHat F E L ≤ (latHat F E L').comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact h a ha x hx
  exact this hu

theorem mulVec_mem_latHat {L L' : Set (Fin k → E)} {δ : Matrix (Fin k) (Fin k) E}
    (h : ∀ v ∈ L, δ *ᵥ v ∈ L') {u : Fin k → Af F ⊗[F] E} (hu : u ∈ latHat F E L) :
    δ.map (inclR (F := F) (Af F)) *ᵥ u ∈ latHat F E L' := by
  refine map_mem_latHat (Matrix.mulVecLin (δ.map (inclR (F := F) (Af F)))).toAddMonoidHom
    (fun b hb x hx => ?_) hu
  convert tmul_mem hb (h x hx) using 1
  funext i
  change ∑ j, ((1 : Af F) ⊗ₜ[F] δ i j : Af F ⊗[F] E) * b ⊗ₜ[F] x j = b ⊗ₜ[F] ∑ j, δ i j * x j
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Adelic

end GlobalTheory.Ker.DCos

end
