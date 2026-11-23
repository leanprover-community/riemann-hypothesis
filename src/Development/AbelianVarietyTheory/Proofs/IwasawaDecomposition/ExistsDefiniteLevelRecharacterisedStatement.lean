module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteLevelRecharacterised
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.exists_definiteLevel_recharacterised : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ τ' : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ), ∃ χ' : M.J →* (NX.Kk D i k)ˣ, (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ M.J, χ' ⟨κ, h⟩ = 1) ∧ NX.HypOutsideF M.J χ' (NX.badV D i Q) ∧ ∀ κ (h : κ ∈ M.J), ((χ' ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ' kv) (NX.locM (M.sp (NX.pG D kv)) κ)) * (∏ P ∈ M.QP, NX.ofOk D i k (NX.tameVal ψ P e (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) * (∏ P ∈ M.DP, NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e else -e) (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) := by
  first | exact @GlobalTheory.LevelRechar.exists_rechar | exact GlobalTheory.LevelRechar.exists_rechar | (intros; apply GlobalTheory.LevelRechar.exists_rechar <;> assumption)
