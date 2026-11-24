module

public import Development.EtaleCohomology.TateTwists.EtaleRestrictScalarsResolutionCompatible
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafRestrictScalarsInjectiveResolutionHomExists : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
    ∃ m : ∀ n : ℤ, (restr φ).obj ((res S F).X n) ⟶ (res R ((restr φ).obj F)).X n,
      (∀ i j : ℤ, (restr φ).map ((res S F).d i j) ≫ m j = m i ≫ (res R ((restr φ).obj F)).d i j) ∧
      (restr φ).map (resι S F) ≫ m 0 = resι R ((restr φ).obj F)

namespace LateralTheory.EtaleFoundations

theorem etaleSheaf_restrictScalars_resolution_comparison_of_hom (hH : EtaleSheafRestrictScalarsInjectiveResolutionHomExists) : EtaleRestrictScalarsResolutionCompatible := by
  intro R S _ _ φ F U a
  obtain ⟨m, hc, h0⟩ := hH R S φ F
  have hex : ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), ∀ (U : Scheme.{0}) (a : Sec F U),
      ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
    refine ⟨⟨fun U s => ((m s).hom.app (op U)).hom.toAddMonoidHom, ?_, ?_⟩, ?_⟩
    · intro V U g s x
      have h := (m s).hom.naturality g.op
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x).symm
    · intro U s t x
      have h := congrArg (fun f : (restr φ).obj ((res S F).X s) ⟶ (res R ((restr φ).obj F)).X t => (f.hom.app (op U)).hom x) (hc s t)
      exact h.symm
    · intro U x
      exact congrArg (fun f : (restr φ).obj F ⟶ (res R ((restr φ).obj F)).X 0 => (f.hom.app (op U)).hom x) h0
  exact pick_spec hex U a

end LateralTheory.EtaleFoundations
