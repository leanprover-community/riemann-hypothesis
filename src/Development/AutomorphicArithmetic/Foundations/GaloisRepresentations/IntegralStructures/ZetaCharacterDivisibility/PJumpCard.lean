module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCount
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
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

theorem UpperTheory.Gal.Int.Div.jumpCard_of :
    JumpCard := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a r hdR τ LL' τ' hτ
  obtain ⟨T⟩ := id tied
  obtain ⟨L₀, r₀, hm, hd⟩ := hdR
  have l₁ : L₀.1 ≤ (supExt L₀ LL').1 := le_sup_left
  have l₂ : LL'.1 ≤ (supExt L₀ LL').1 := le_sup_right
  have hm' := hm.enlarge l₁
  have hd' := (local_ext P Bw l₁ r₀).2.1.2 hd
  have hτ' : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ') := fun x => hτ x
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀)) := by
    rw [IsDR, Module.finrank_fin_fun]
    exact hd'
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ (supExt L₀ LL') _
    (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀))).1
      ((IntermediateField.inclusion l₂).comp τ')
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _
    ((mapRep (IntermediateField.inclusion l₁).toRingHom r₀).comp Bw.e.symm.toMonoidHom)
    ((IntermediateField.inclusion l₂).comp τ') hfin
  exact ⟨J', ⟨_, _, hm', hd', _, hτ', h2⟩, h1.trans ((hrk hdr').trans (Module.finrank_fin_fun _))⟩
