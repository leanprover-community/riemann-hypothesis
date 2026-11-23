module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLevelFormsIffStdGroupTypeSpace
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.definiteLevelForms_iff_stdGroupTypeSpace : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → UnitFr P → RatIso P e → ∀ (G₀ : Type) [Group G₀] (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ F : Bridge.Gf V → c.W, F ∈ cutSp (Bridge.ratF V) c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch red P₀ ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ↔ (fun g => F (toGf P g)) ∈ NG.TypeSp (wtRep c e) (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) := by
  first | exact @GlobalTheory.MtInType.cutSp_iff_typeSp | exact GlobalTheory.MtInType.cutSp_iff_typeSp | (intros; apply GlobalTheory.MtInType.cutSp_iff_typeSp <;> assumption)
