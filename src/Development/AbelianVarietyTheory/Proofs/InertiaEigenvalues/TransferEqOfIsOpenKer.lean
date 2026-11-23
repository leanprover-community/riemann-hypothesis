module

public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Formalism.ConjugateSelfDual.Statement
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransfer

open scoped Pointwise
open UpperTheory.V.Base (galOf galEmb galEmbTop range_galEmb galEmb_mem)
open Formalism.L2.Host (IsUnitAt IsUnifAt aboveF)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

section Group

variable {Γ B : Type} [Group Γ] [CommGroup B] {H : Subgroup Γ} [H.FiniteIndex] (φ : H →* B)

end Group

section Places

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]


variable [Algebra K L] [IsScalarTower K L Ω]

end Places

section Ideles

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {K} in
theorem loc_same (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

variable {K} in
theorem loc_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleMap_apply (a : Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (ideleMap K L a).val.2 w = finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

end Ideles

section Artin

variable {K L Ω B : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [CommGroup B]

variable [Algebra K L]


variable [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

end Artin

end GlobalTheory.ArtinTransfer

end
