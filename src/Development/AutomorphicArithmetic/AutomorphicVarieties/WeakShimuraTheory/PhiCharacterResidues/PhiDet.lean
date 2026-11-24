module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeterminantIdentities
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiDet :
    ∀ {n : ℕ} {B A H G : Type} [CommRing B] [CommRing A] [Group H] [Group G] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace G] (I : Ideal B) [IsHausdorff I B] (f : B →+* A), Function.Injective f → ∀ (π : H →* G), Function.Surjective π → Topology.IsQuotientMap π → ∀ (ρ : H →* Matrix (Fin n) (Fin n) A) (cp : H → B[X]), (∀ g, (cp g).map f = (ρ g).charpoly) → (∀ j, AdicCont I fun g => (cp g).coeff j) → (∀ U : Subgroup H, IsClosed (U : Set H) → ρ.ker ≤ U → π.ker ≤ U) → ∃ D : W.GDet n B G, (D.comap π).map f = W.GDet.ofRep ρ ∧ (∀ g, D.chi (MonoidAlgebra.single (π g) 1) = cp g) ∧ D.IsCont I :=
  _root_.UpperTheory.Reformulated.B.DeterminantIdentities.phiDet
