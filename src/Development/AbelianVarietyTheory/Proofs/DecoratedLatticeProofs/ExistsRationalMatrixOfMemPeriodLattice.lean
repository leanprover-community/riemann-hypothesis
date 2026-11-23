module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.LamPre

theorem exists_mat_of_mem_lamC : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧ embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := by
  intro D S T a b hS hT δ N N' x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx
  refine ⟨(LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm, ?_, ?_, ?_⟩
  · have e : toHom S T hS hT ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm) = y := by
      unfold toHom
      rw [show ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm).reindex (finCongr hT) (finCongr hS)
          = LinearMap.toMatrix' y from by ext i j; simp, Matrix.toLin'_toMatrix']
    rw [e]; exact hy
  · have e : toHom S T hS hT ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm) = y := by
      unfold toHom
      rw [show ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm).reindex (finCongr hT) (finCongr hS)
          = LinearMap.toMatrix' y from by ext i j; simp, Matrix.toLin'_toMatrix']
    rw [e]
  · exact ⟨GlobalTheory.VacUnique.finRat S T _, GlobalTheory.VacUnique.finRat_inf S T _, GlobalTheory.VacUnique.finRat_fin S T _⟩

end GlobalTheory.AdForm.LamPre
