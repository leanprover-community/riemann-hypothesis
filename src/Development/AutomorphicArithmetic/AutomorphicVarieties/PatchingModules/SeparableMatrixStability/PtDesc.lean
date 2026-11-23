module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.BDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.NpDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PtUnip
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pt_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (r' : Resid Q.G0'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (D0 : ℕ) (P : Pt T u D0), Adapted T (r := r) → Glob.Compat Q.g0 r r' → u'.D.comap Q.g0.p₀ = u.D → u'.ψ = u.ψ → ∃ P' : Pt Q.grp u' D0, RingHom.ker P'.f = RingHom.ker P.f ∧ Nat.card P'.x.K = Nat.card P.x.K := by
  intro l _ L G0 T Q n O _ _ _ r r' B _ _ _ u u' D0 P hA hC hD hψ
  have hU := UpperTheory.V.Pa.pt_unip l L G0 T n O r B u D0 P hA
  obtain ⟨⟨ρ', hρ⟩, κ', hκ⟩ := UpperTheory.V.Pa.np_desc l L G0 Q.G0' Q.g0 n P.x P.k
    (T.H.toOpenSubgroup : Subgroup G0.Γ) T.H.toOpenSubgroup.isOpen'
    (fun g hg => MonoidHom.mem_ker.2 (T.H_η g hg)) hU Q.ker0
  have hb := UpperTheory.V.Pa.b_desc l L G0 T Q n P.x P.k ρ' hρ κ' hκ D0 hU
  letI := P.alg
  have hmat : (mat ρ').comp Q.g0.p₀ = mat P.x.ρ := by
    ext a i j
    simp [mat, hρ]
  refine ⟨⟨NP.desc Q.g0 P.x ρ' hρ, Kap.desc Q.g0 ρ' hρ P.k κ' hκ, P.al, ?_, hb.1 P.b1, hb.2 P.b2,
    P.f, ?_⟩, rfl, rfl⟩
  · intro j
    obtain ⟨h1, h2⟩ := P.eig j
    refine ⟨h1, ?_⟩
    have e : (mat ρ') (Q.g0.p₀ (T.sg j)) = (mat P.x.ρ) (T.sg j) := by
      rw [← hmat]
      rfl
    exact e ▸ h2
  · refine ⟨?_, fun v i => by rw [hψ]; exact P.maps.2 v i⟩
    obtain ⟨-, -, -, -, hof, hsurj⟩ := UpperTheory.V.Pa.comap_lam n P.x.A G0.G₀ Q.G0'.G₀ Q.g0.p₀
      (GDet.ofRep (mat ρ'))
    obtain ⟨-, -, -, hmap, -, -⟩ := UpperTheory.V.Pa.comap_lam n B G0.G₀ Q.G0'.G₀ Q.g0.p₀ u'.D
    apply (hsurj (Glob.Hom.p₀_surj Q.g0)).1
    rw [← hmap, hD, P.maps.1, hof (mat ρ'), hmat]
