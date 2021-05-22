import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product using (Σ; _×_; ∃; ∃-syntax; Σ-syntax) renaming (_,_ to ⟨_,_⟩)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
  
-- + (Addition)
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- ∸ (Monus)
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

-- * (Multiplication)
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n  = n + (m * n)

-- ^ (Exponentiation)
_^_ : ℕ → ℕ → ℕ
m ^ zero = (suc zero)
m ^ (suc n) = m * (m ^ n)

infixl 6 _+_ _∸_
infixl 7 _*_
infixl 8 _^_

-- Addition: Associativity
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p = 
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- Addition: Right Identity Zero 
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = 
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc x) = 
  begin
    suc x + zero
  ≡⟨⟩
    suc (x + zero)
  ≡⟨ cong suc (+-identityʳ x) ⟩
    suc x
  ∎

-- Addition: Preposition of Suc
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
   zero + suc n
 ≡⟨⟩
   suc n
 ≡⟨⟩
   suc (zero + n)
 ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- Addition: Commutativity
+-comm  : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Addition: Rearrangement
+-rearrange  : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q))  ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎


-- Addition: Associativity (2nd proof)
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

-- Addition: Right Identity (2nd proof)
+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-identityˡ : ∀ (n : ℕ) → zero + n ≡ n
+-identityˡ n rewrite +-comm zero n = refl

-- Addition: Preposition of Suc (2nd proof)
+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

-- Addition: Commutativity (2nd proof)
+-comm′ : ∀ (m n : ℕ) →  m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Addition: Swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

-- Multiplication: Right Distributivity over Addition
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl

-- Multiplication: Associativity
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

-- Multiplication: Right Zero
*-zero : ∀ (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) rewrite *-zero n = refl

-- Multiplication: Preposition of Suc
*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n rewrite *-zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

-- Multiplication: Right Identity
m*1≡m : ∀ (m : ℕ) → m * (suc zero) ≡ m 
m*1≡m m rewrite *-suc m zero | *-zero m | +-identityʳ m = refl

-- Multiplication: Commutativity
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zero n = refl
*-comm (suc m) n rewrite *-suc n m | *-comm m n = refl

-- Multiplication: Swap
*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap m n p rewrite sym (*-assoc m n p) | *-comm m n | *-assoc n m p = refl

-- Monus: Left Identity
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

-- Monus: Right Associativity with Addition
∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p)= refl
∸-|-assoc (suc m) zero p = refl
∸-|-assoc (suc m) (suc n) p rewrite ∸-|-assoc m n p = refl

-- Exponentiation: Left Distributivity over Addition
^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identityʳ (m ^ p)= refl
^-distribˡ-|-* m (suc n) p rewrite ^-distribˡ-|-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

-- Exponentiation: Right Distributivity over Multiplication
^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite
    ^-distribʳ-* m n p |
    *-assoc m n ((m ^ p ) * (n ^ p)) |
    *-swap n (m ^ p) (n ^ p) |
    *-assoc m (m ^ p) (n * (n ^ p))
    = refl

-- Exponentiation: Right Associativity with Multiplication
^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-zero n = refl
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p | sym (^-distribˡ-|-* m n (n * p)) | *-suc n p  = refl


-- Negated Equality
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

-- Monus: Non-commutativity 
¬∸-assoc : ∀ {m n : ℕ} → m ≢ n → (m ∸ n) ≢ (n ∸ m)
¬∸-assoc {zero} {zero} m≢n = m≢n
¬∸-assoc {suc m} {suc n} sm≢sn m∸n≡n∸m = (¬∸-assoc λ{m≡n → sm≢sn (cong suc m≡n)}) m∸n≡n∸m

-- ||: Divides
data _||_ : ℕ → ℕ → Set where
  div : ∀ {m n} → Σ[ x ∈ ℕ ] (m * x ≡ n) → m || n

-- Divides: Reflexivity
||-refl : ∀ (m : ℕ) → m || m 
||-refl m = div ⟨ suc zero , m*1≡m m ⟩

-- Divides: Transitivity
||-trans : ∀ {m n p : ℕ} → m || n → n || p → m || p
||-trans {m} {n} {p} (div ⟨ fst , snd ⟩) (div ⟨ fst₁ , snd₁ ⟩) = div ⟨ fst * fst₁ , *-trans {m} {n} {p} {fst} {fst₁} snd snd₁ ⟩ where
  *-trans : ∀ {m n p f f1} → m * f ≡ n → n * f1 ≡ p → m * (f * f1) ≡ p
  *-trans {m} {n} {p} {f} {f1} mfn nf1p rewrite sym (*-assoc m f f1) | mfn | nf1p = refl

  

