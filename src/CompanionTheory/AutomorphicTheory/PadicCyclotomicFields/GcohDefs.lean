module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import GroundTheory.ProfiniteCohomology.CupProducts
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
public import Mathlib.NumberTheory.LocalField.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

def SgcRep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M), ContAction rho → ∃ (A : Rep.{0} (ULift.{0} ℤ) G) (_ : IsDiscreteRep A) (e : M ≃+ A.V), ∀ g m, e (rho g m) = A.ρ g (e m)

def Sgc0 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e0 : ↥(H0 rho) ≃+ cohomology A 0, ∀ (m : ↥(H0 rho)) (x : cocycles A 0), (∀ s, cochainOf A (cocycleι A 0 x) s = e m.1) → e0 m = cohomologyπ A 0 x

def Sgc1 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e1 : H1 rho ≃+ cohomology A 1, (∀ z : ↥(Z1 rho), ∃ x : cocycles A 1, ∀ s, cochainOf A (cocycleι A 1 x) s = e (z.1 (s 0))) ∧ ∀ (z : ↥(Z1 rho)) (x : cocycles A 1), (∀ s, cochainOf A (cocycleι A 1 x) s = e (z.1 (s 0))) → e1 (Submodule.Quotient.mk z) = cohomologyπ A 1 x

def Sgc2 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e2 : H2 rho ≃+ cohomology A 2, (∀ z : ↥(Z2 rho), ∃ x : cocycles A 2, ∀ s, cochainOf A (cocycleι A 2 x) s = e (z.1 (s 0, s 1))) ∧ ∀ (z : ↥(Z2 rho)) (x : cocycles A 2), (∀ s, cochainOf A (cocycleι A 2 x) s = e (z.1 (s 0, s 1))) → e2 (Submodule.Quotient.mk z) = cohomologyπ A 2 x

def Sgcn : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∀ n : ℕ, Nonempty (Hn rho n ≃+ cohomology A n)

def SgcField : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → IsSepClosure ↥K (PadicAlgCl l) ∧ ∃ (_ : ValuativeRel ↥K) (t : TopologicalSpace ↥K), @IsNonarchimedeanLocalField ↥K _ _ t ∧ ∀ m : ℕ, Nat.card (𝒪[↥K] ⧸ Ideal.span {((l ^ m : ℕ) : 𝒪[↥K])}) = (l ^ m) ^ Module.finrank ℚ_[l] ↥K

def SgcMu : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : ℕ), ∃ e : ZMod (l ^ r) ≃+ (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).V, ∀ (g : Formalism.GaloisCohomology.GK l K) (m : ZMod (l ^ r)), e ((Formalism.GaloisCohomology.cycK l K r g : ZMod (l ^ r)) * m) = (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).ρ g (e m)

end CompanionTheory.LocalTateOrthogonality.Gcoh
