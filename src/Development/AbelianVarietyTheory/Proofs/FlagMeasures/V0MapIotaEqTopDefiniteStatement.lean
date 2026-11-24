module

public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.V0MapIotaEqTopDefinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField

theorem _root_.GlobalTheory.T.V0_map_iota_eq_top_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @GlobalTheory.V0_map_iota_eq_top_of_definite | exact GlobalTheory.V0_map_iota_eq_top_of_definite | (intros; apply GlobalTheory.V0_map_iota_eq_top_of_definite <;> assumption)
