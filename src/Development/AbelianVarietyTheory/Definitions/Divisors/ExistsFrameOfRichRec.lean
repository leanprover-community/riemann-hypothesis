module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn.CoreWit

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.JoinChr in
theorem exists_val_of_chrEq {c : (Formalism.L2.Theta.AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ)
    (x : (Formalism.L2.Theta.AE D)ˣ) : ∃ y, ((c x : Circle) : ℂ) = ((χ.1 y : ℂˣ) : ℂ) := by
  have hχ := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.2 c χ h
  obtain ⟨Θ, hc, hinc, hloc⟩ := GlobalTheory.CharTransport.exists_hom D
  let u : (Formalism.L2.Theta.AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (Formalism.L2.Theta.AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have h' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · refine (hcoe _).trans ?_
      have := congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ))
        (Units.ext (hinc x) : u (Units.map (Formalism.L2.Theta.incA D).toMonoidHom x) = Units.map (algebraMap D.host.E _).toMonoidHom x)
      exact this.trans (congrArg (fun y : ℂˣ => (y : ℂ)) (χ.2.2 x))
    · refine (hcoe _).trans (congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ)) (Units.ext ?_))
      change Θ (x : Formalism.L2.Theta.AE D) = _
      rw [hx, hloc P e he]
  exact ⟨u x, by rw [(GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 c c' χ h h', hcoe]⟩

end GlobalTheory.BigOn.CoreWit

end
