module

public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NearConstantMultiplicities
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsBaseLevel
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section End3

open Formalism.IndefR.Cx Formalism.L2.Geo Formalism.MainNotions

variable [_root_.NumberField.IsTotallyComplex D.what₂.LL] {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def PassIn3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (C CH : ℝ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module D.what₂.LL (Ws s))
    (_ : ∀ s, FiniteDimensional D.what₂.LL (Ws s)) (τ : ∀ s, Representation D.what₂.LL G (Ws s)) (nbar : ℝ),
    CxPassIn3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) C CH S Ws τ nbar

def primitivePackageFullHecke {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (H : HkDat3 A3) (C CH : ℝ) (hC : R.WeakCharacterisation F)
    (hP : CovolumeOntoIsometryConditions R F sEE H C CH) (hI : PassIn3 R F C CH) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (R.convOf F H) C CH :=
  letI := hI.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  packageFullHecke (base_lifts_package_of_primitive_links hOk hsep hC hP) hI.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

def primRows3 {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    (hP : PrimRows3 R F) : IndefRows (lv (F.fc (R.toCx3 F).zs) false) :=
  indefiniteDataAtBaseLevel (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP)

theorem primRows3_data {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) : (primRows3 hOk hsep R F hC hP).toIndefData = (R.toCx3 F).data F.cr false := rfl

end End3

end Formalism.IndefR.Links

end
