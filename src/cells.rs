/*!

  Traits to abstract mapping symbols to gates.

*/

use safety_net::error::Error;

/// A trait to specify how to map primitive instantiation names ([Identifier]s) to the instance [Instantiable] type.
pub trait FromId: Sized {
    /// Maps primitive instantiation names ([Identifier]s) to the instance [Instantiable] type.
    fn from_id(s: &safety_net::circuit::Identifier) -> Result<Self, Error>;
}
