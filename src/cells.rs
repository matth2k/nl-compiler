/*!

  Traits to abstract mapping symbols to gates.

*/

use safety_net::Error;
use safety_net::Identifier;

/// A trait to specify how to map primitive instantiation names ([Identifier]s) to the instance [safety_net::Instantiable] type.
pub trait FromId: Sized {
    /// Maps primitive instantiation names ([Identifier]s) to the instance [safety_net::Instantiable] type.
    fn from_id(s: &Identifier) -> Result<Self, Error>;
}
