module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCharAnn
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem aeval_matrix_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (Q : K[X]) :
    aeval (M.map f) (Q.map f) = (aeval M Q).map f := by
  simp only [aeval_def, eval₂_map]
  have h := hom_eval₂ Q (algebraMap K (Matrix (Fin n) (Fin n) K)) f.mapMatrix M
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h]
  congr 1
  ext a : 1
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map]

theorem UpperTheory.Gal.Int.Div.genPin_of :
    GenPin := by
  intro l _ ι a M s hcard hgen hann hdet
  set P := (Multiset.map (fun b ↦ X - C b) s).prod with hPdef
  have hround : map ι.toRingHom (map ι.symm.toRingHom P) = P := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext z
    simp
  have hann2 : aeval (M.map ι.toRingHom) (UpperTheory.Gal.crystallineComparison.rootPol s) = 0 := by
    show aeval (M.map ι.toRingHom) P = 0
    rw [← hround, aeval_matrix_map, hann]
    simp
  have hdet2 : (M.map ι.toRingHom).det = s.prod := by
    have hd := RingHom.map_det ι.toRingHom M
    rw [RingHom.mapMatrix_apply] at hd
    rw [← hd]
    exact hdet
  rw [← Matrix.charpoly_map]
  exact UpperTheory.Gal.crystallineComparison.charAnn_of ℂ a _ s hcard hgen hann2 hdet2
