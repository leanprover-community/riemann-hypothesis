module

public import Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi
public import Formalism.LocalToGlobal.HermitianForms.TransportT

@[expose] public section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7}

def EvzTie {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    {Tl : TilTied u A K P} {Km : ClsTied u D.R.m le_rfl}
    (Ta : TilAd Tl Km) (W : ValTied u A.eV D.R.m le_rfl Km)
    (eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)) : Prop :=
  ∀ (φ : (D.mem u).C.cls D.R.m → (D.mem u).C.Y D.R.m → ℂ) c s s',
    IsTr (atInf (embT D) (Tl.ga c).1.1) (W.eY s') (W.eY s) →
    eWz ((D.mem u).P.evz φ) c s = (((Km.lev.chi (Ta.ka c))⁻¹ : ℂˣ) : ℂ) * φ ((D.fm u).til c) s'

open Classical in
def BwTie {u : D.what₂.Word} (A : AtTTied u) {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u A.eV i hi K) : Prop :=
  ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (D.fm u).seenP w = true →
    ∀ v (x : ((D.fm u).lat i).V), x ∈ (D.fm u).Bw i w v ↔
    ∀ (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B → IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B' →
      ∃ P ∈ IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i x c z =
        fnOf _ (shiftOf (lamT u i))
          (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ
            else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ) P (W.eY z)

def PerTie (u : D.what₂.Word) (jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow) : Prop :=
  (∀ z ∈ (D.fm u).ptC, ∃ F, jM F = z) ∧ (∀ F, jM F ∈ (D.fm u).ptC) ∧
    ∀ w F, (D.mem u).P.period w F = (D.fm u).ipP (jM F) w

def subP {ι : Type} {n : ℕ} (o : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  MvPolynomial.aeval fun x => ∑ a', MvPolynomial.C (o x.1 x.2.1 a') * MvPolynomial.X (x.1, a', x.2.2)

def embS (D : D7) (s : D.what₂.LL →+* ℂ) : D.what₂.Tau → D.host.E →+* ℂ :=
  fun τ => s.comp (D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

def NormTie {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u eV i hi K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : ((D.fm u).lat i).V)
    (Pc : (D.mem u).C.cls i → MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) D.what₂.LL),
    (∀ c z, (D.fm u).emb i x c z =
      fnOf _ (shiftOf (lamT u i)) 1 (MvPolynomial.map D.what₂.embLL (Pc c)) (W.eY z)) →
    ∀ o : Frames (gramC (gramN D i hi) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk s) x x).re =
        ∑ c, ((D.mem u).C.wt i c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u i) τ)) *
          (nfAll ((D.fm u).lam i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def NormPTie {u : D.what₂.Word} {K : ClsPTied u} (W : ValPTied u K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : (D.fm u).ptLat.V)
    (Pc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW ((D.fm u).ptEmb x) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (nfAll (D.fm u).sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def aOf (R : Ranks) (i : ℕ) : ℕ := if i < R.m then R.k + i else R.r

theorem Mu0_iff {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :
    φ ∈ (D.mem u).A.Mu0 ↔
      (fun c z => φ c (W.eY.symm z)) ∈ FiC K.lev (embT D) ((D.fm u).lam 0) K.y := by
  rw [← (D.fm u).Fi_zero, ← lamT_zero]; exact W.Fi φ

theorem rhoT_eq {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia K.lev (eV v).1 (eV v).2 k δ) (g) (hg : g ∈ AdFun K.lev (embT D)) :
    (D.mem u).A.rhoT v a (fun c s => g (K.y c) (W.eY s)) = fun c s => g (K.y c * δ) (W.eY s) := by
  funext c
  rw [(D.fm u).rhoT_dil]
  exact W.dilT v a k hk c δ hδ g hg

end Formalism.L2.Forms
