module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOpFace

theorem heckeOp_face_to_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (b : Bool) (i : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (B : Finset (GA D (Wc D i))), Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) SF P d B → Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF b i P d B hB
  have hS : OffS D SF P := by
    obtain ⟨_, _, _, _, hS, -⟩ := hB
    exact hS
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.1 SF hSF P).1 hS
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hPP : ∀ L : LevelP R.Pg D.R.r ℂ, ∀ PP, PP ∈ (R.datWp i L).Pg ∨ PP ∈ (R.datWp i L).Q →
      PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := fun L PP h =>
    hG PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  have h1 := ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n)
    (R.datWp i (R.levL F b (sg0 D A))) hβ P hN (hPP _)).2.1 SF d B).1 hB
  exact ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P hN (hPP _)).2.1 SF d B).2 h1

end GlobalTheory.LevOpFace
