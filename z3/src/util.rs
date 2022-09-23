use Context;

pub fn retrieve_iter<'ctx, T> (
    ctx: &'ctx Context,
    len_cb: &dyn Fn() -> usize,
    single_cb: &dyn Fn(usize) -> T
) -> Vec<T>
{
    let len = len_cb();
    let mut result = Vec::with_capacity(len);
    for i in 0..len {
        let elem = single_cb(i);
        result.push(elem);
    }

    result
}