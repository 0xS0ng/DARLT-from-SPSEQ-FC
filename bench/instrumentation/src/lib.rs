//! Optional source instrumentation; arithmetic stays in the original backend.
use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::{parse_macro_input, spanned::Spanned, visit_mut::VisitMut, BinOp, Expr, Item};

struct CountMultiplications;

impl VisitMut for CountMultiplications {
    fn visit_expr_mut(&mut self, expression: &mut Expr) {
        syn::visit_mut::visit_expr_mut(self, expression);
        let Expr::Binary(binary) = expression else {
            return;
        };
        fn unparenthesized(mut expression: &Expr) -> &Expr {
            while let Expr::Paren(inner) = expression {
                expression = &inner.expr;
            }
            expression
        }
        let span = binary.span();
        let left = unparenthesized(&binary.left);
        let right = unparenthesized(&binary.right);
        // Preserve contextual integer inference for constant-only arithmetic.
        // Neither operand can be a group value in this case.
        if matches!(left, Expr::Lit(_)) && matches!(right, Expr::Lit(_)) {
            return;
        }
        let replacement = match binary.op {
            BinOp::Mul(_) => quote_spanned!(span=> crate::ops::mul(#left, #right)),
            BinOp::MulAssign(_) => {
                quote_spanned!(span=> crate::ops::mul_assign(&mut #left, #right))
            }
            _ => return,
        };
        *expression = syn::parse2(replacement).expect("instrumented multiplication expression");
    }

    // syn treats macro tokens as opaque. vec! is a container for expressions,
    // so parse both its comma-separated and repetition forms explicitly.
    fn visit_macro_mut(&mut self, invocation: &mut syn::Macro) {
        if invocation
            .path
            .segments
            .last()
            .is_none_or(|part| part.ident != "vec")
        {
            return;
        }
        let original = &invocation.tokens;
        let Ok(mut array) = syn::parse2::<Expr>(quote!([#original])) else {
            return;
        };
        self.visit_expr_mut(&mut array);
        invocation.tokens = match array {
            Expr::Array(array) => {
                let elements = array.elems;
                quote!(#elements)
            }
            Expr::Repeat(repetition) => {
                let value = repetition.expr;
                let length = repetition.len;
                quote!(#value; #length)
            }
            _ => unreachable!("vec expression parser"),
        };
    }
}

/// Attach through `cfg_attr(feature = "op-counts", instrument_ops::count_ops)`
/// to a function or an impl block. No macro is loaded in the timing build.
#[proc_macro_attribute]
pub fn count_ops(arguments: TokenStream, input: TokenStream) -> TokenStream {
    if !arguments.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "count_ops takes no arguments",
        )
        .to_compile_error()
        .into();
    }
    let mut item = parse_macro_input!(input as Item);
    CountMultiplications.visit_item_mut(&mut item);
    quote!(#item).into()
}
