module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistDataLowerBlockUniversalCharacter
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.exists_twistData_lowerBlock_universalCharacter : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ) (τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ), (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∃ N : TwNew D, N.tw = D.ntw ∧ (GlobalTheory.HeightCounting.SerCopy.NoOff D → GlobalTheory.HeightCounting.SerCopy.NoOff N.toD7) ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧ ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  first | exact @GlobalTheory.TrueTau.exists_trueTau | exact GlobalTheory.TrueTau.exists_trueTau | (intros; apply GlobalTheory.TrueTau.exists_trueTau <;> assumption)
