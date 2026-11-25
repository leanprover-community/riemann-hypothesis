module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePullbackOfRaynaudTorusWeightZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.RayLift

theorem exists_flat_lift (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (z : (DegPre.BF Q (FractionRing R)).left) :
    ∃ (Z : Scheme.{0}) (p : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (w : Z) (y : Z ⟶ Y.H.left),
      p w = z ∧ Epi p ∧ Function.Injective (p.stalkMap w).hom ∧
        y ≫ Y.q.left = p ≫ (DegPre.prB Q (FractionRing R)).left := by
  obtain ⟨hF, hS, -⟩ := GlobalTheory.Heat.Descend.q_props Y
  let p := pullback.fst (DegPre.prB Q (FractionRing R)).left Y.q.left
  have hpF : Flat p := by haveI := hF; dsimp [p]; infer_instance
  have hpS : Surjective p := by haveI := hS; dsimp [p]; infer_instance
  obtain ⟨w, hw⟩ := p.surjective z
  refine ⟨_, p, w, pullback.snd _ _, hw, Flat.epi_of_flat_of_surjective p, ?_, pullback.condition.symm⟩
  let _ := (p.stalkMap w).hom.toAlgebra
  have : Module.Flat _ _ := Flat.stalkMap p w
  have : IsLocalHom (algebraMap ((DegPre.BF Q (FractionRing R)).left.presheaf.stalk (p w)) ((pullback (DegPre.prB Q (FractionRing R)).left Y.q.left).presheaf.stalk w)) :=
    inferInstanceAs (IsLocalHom (p.stalkMap w).hom)
  have : Module.FaithfullyFlat ((DegPre.BF Q (FractionRing R)).left.presheaf.stalk (p w)) ((pullback (DegPre.prB Q (FractionRing R)).left Y.q.left).presheaf.stalk w) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective _ _

end GlobalTheory.RayLift
