module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SmoothCharDet

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

theorem isSmoothChar_of_detChar_apow_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  intro k _ _ _ _ n hn ν s P hP hν
  let i0 : Fin n := ⟨0, hn⟩
  let d : kˣ →* GL (Fin n) k :=
    (diagHom (k := k) (n := Fin n)).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i0)
  have hval : Continuous fun x : kˣ => ((d x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    show Continuous fun x : kˣ => diagonal fun i => (((Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x) i : kˣ) : k)
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp ((continuous_apply i).comp (continuous_mulSingle (A := fun _ : Fin n => kˣ) i0)))
  have hd : Continuous d := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have := hval.comp continuous_inv
    simpa [Function.comp_def, map_inv] using this
  have hdet : ∀ x : kˣ, gdet (d x) = x := fun x => by
    show Matrix.GeneralLinearGroup.det (diagGL (Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x)) = x
    rw [det_diagGL]
    simp
  have hU : (d : kˣ → GL (Fin n) k) ⁻¹' (P ∩ (KO k (Fin n) : Set (GL (Fin n) k))) ∈ 𝓝 (1 : kˣ) := by
    refine hd.continuousAt.preimage_mem_nhds ?_
    rw [map_one]
    exact Filter.inter_mem hP (isOpen_KO.mem_nhds (one_mem _))
  refine Subgroup.isOpen_of_mem_nhds ν.ker (Filter.mem_of_superset hU fun x hx => ?_)
  have h1 := hν _ hx.1
  rw [apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.2), mul_one, hdet] at h1
  exact MonoidHom.mem_ker.2 (Units.ext h1)

end GlobalTheory.SmoothCharDet
