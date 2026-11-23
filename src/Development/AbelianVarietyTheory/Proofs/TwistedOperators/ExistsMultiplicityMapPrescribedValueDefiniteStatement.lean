module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicityMapPrescribedValueDefinite
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_multiplicityMap_prescribed_value_definite : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsInfFam θ → V.SigOK → V.IsDefinite → c.Is → IsDualPair θ M c pr → Function.Surjective pr → (∀ x, levFn β (flag1L L) x = 1) → (∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) → ∀ (h : GA D V) (ℓ : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∃ T ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)), evAt M h T = ℓ ∧ ∀ h' : GA D V, clsA V (lev D.sp.cm V.gram β (flag1L L)) h' ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h → evAt M h' T = 0 := by
  first | exact @GlobalTheory.DefFree.exists_mult_value | exact GlobalTheory.DefFree.exists_mult_value | (intros; apply GlobalTheory.DefFree.exists_mult_value <;> assumption)
