module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelsReadOnProductPrimeFieldGL
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

theorem _root_.GlobalTheory.T.levels_read_on_product_primeFieldGL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.IsGrp F → ∀ b : Bool, ∃ (Φ : G ≃* GProd D) (L₁ : D.nd.PlG 0 → GlobalTheory.BadShare.Lev (D.host.g 0) D.R.r) (L₂ : D.nd.PlG 1 → GlobalTheory.BadShare.Lev (D.host.g 1) D.R.r), (∀ g : G, g ∈ (F.lvl b).P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) ∧ (∀ g : (F.lvl b).P, D.what₂.embLL (((F.lvl b).ψ⁻¹ g : D.what₂.LLˣ) : D.what₂.LL) = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) ∧ (∀ g : G, GlobalTheory.BadShare.AllUnip (Φ g).1 ∨ GlobalTheory.BadShare.AllUnip (Φ g).2 → ∃ (k : Fin 2) (PP : R.Pg), CharP (kP PP.1) (D.host.g k) ∧ IsNilpotent ((R.eG g PP).val - 1)) ∧ ∀ (g : G) (γ : G0g D.nd), (∀ v, γ ⟨0, v⟩ = (Φ g).1 v) → (∀ v, γ ⟨1, v⟩ = (Φ g).2 v) → D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff γ := by
  first | exact @GlobalTheory.LevelsProd.levels_prod | exact GlobalTheory.LevelsProd.levels_prod | (intros; apply GlobalTheory.LevelsProd.levels_prod <;> assumption)
