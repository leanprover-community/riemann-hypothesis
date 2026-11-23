module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelUnipotentGenericCharTypePlace
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levelUnipotent_genericChar_typePlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi L.Pg ψ → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w ∈ L.Pg → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelUni (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ψ₀ ξ := by
  first | exact @GlobalTheory.TypeLevelUni.levelUni_typePlace | exact GlobalTheory.TypeLevelUni.levelUni_typePlace | (intros; apply GlobalTheory.TypeLevelUni.levelUni_typePlace <;> assumption)
