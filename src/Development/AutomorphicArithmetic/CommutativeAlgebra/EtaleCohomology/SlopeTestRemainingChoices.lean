module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Et

structure SlopeTestRemainingChoices : Prop where
  sheaf : type_of% @GlobalTheory.T.etaleSheafSections_ext_and_glue
  resol : type_of% @GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness
  freeS : type_of% @GlobalTheory.T.free_sections_ext_res_map
  evs : type_of% @GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties
  rep : type_of% @GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff
  sec : type_of% @GlobalTheory.T.degreeZeroSectionClass_properties
  aw : type_of% @GlobalTheory.T.cup_eq_class_of_isAW
  twist : type_of% @GlobalTheory.T.tateTwist_sections_locally_generated
  pair : type_of% @GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique
  unit : type_of% @GlobalTheory.T.tateTwistUnitClass_rootClass_spec

section Site
variable {C : Type 1} [Category.{0} C] {S : Type 1} [CommRing S]

abbrev PM (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] : Type 2 := Cᵒᵖ ⥤ ModuleCat.{1} S

structure Dat (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] (ι : Type) where
  P : ι → ℤ → PM C S
  dP : ∀ b s t, P b s ⟶ P b t
  Q : ℤ → PM C S
  dQ : ∀ s t, Q s ⟶ Q t
  e : ι → ℤ
  φ : ∀ b s, P b (s - e b) ⟶ Q s
  ddP : ∀ b s t u, dP b s t ≫ dP b t u = 0
  ddQ : ∀ s t u, dQ s t ≫ dQ t u = 0
  comm : ∀ b s t, s + 1 = t → φ b s ≫ dQ s t = dP b (s - e b) (t - e b) ≫ φ b t

variable {ι : Type} [Fintype ι] (D : Dat C S ι)

end Site

section Rep
variable {R : Type} [CommRing R]

def Rep {I : Cx R} {U : Scheme.{0}} {n : ℤ} (z : Sec (I.X n) U) (c : CohomologyClass ((chains R).obj (sch.obj U)) I n) : Prop :=
  ∃ α : Cocycle ((chains R).obj (sch.obj U)) I n, CohomologyClass.mk α = c ∧ ev α.1 0 n (by simp) U (𝟙 U) = z

variable {S Y : Scheme.{0}} (p' : Y ⟶ S)

end Rep

section Classes
variable (q : ℕ) {S Y : Scheme.{0}} (p' : Y ⟶ S) {ι : Type} [Fintype ι] {e : ι → ℤ} {j : ℤ} (w : ∀ b, Ht q (sch.obj Y) (e b) j)

end Classes

end UpperTheory.Et

end
