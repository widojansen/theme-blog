function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function prevent_default(fn) {
    return function (event) {
        event.preventDefault();
        // @ts-ignore
        return fn.call(this, event);
    };
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_in_transition(node, fn, params) {
    const options = { direction: 'in' };
    let config = fn(node, params, options);
    let running = false;
    let animation_name;
    let task;
    let uid = 0;
    function cleanup() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function go() {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        if (css)
            animation_name = create_rule(node, 0, 1, duration, delay, easing, css, uid++);
        tick(0, 1);
        const start_time = now() + delay;
        const end_time = start_time + duration;
        if (task)
            task.abort();
        running = true;
        add_render_callback(() => dispatch(node, true, 'start'));
        task = loop(now => {
            if (running) {
                if (now >= end_time) {
                    tick(1, 0);
                    dispatch(node, true, 'end');
                    cleanup();
                    return running = false;
                }
                if (now >= start_time) {
                    const t = easing((now - start_time) / duration);
                    tick(t, 1 - t);
                }
            }
            return running;
        });
    }
    let started = false;
    return {
        start() {
            if (started)
                return;
            started = true;
            delete_rule(node);
            if (is_function(config)) {
                config = config(options);
                wait().then(go);
            }
            else {
                go();
            }
        },
        invalidate() {
            started = false;
        },
        end() {
            if (running) {
                cleanup();
                running = false;
            }
        }
    };
}
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let meta0;
	let meta0_content_value;
	let t;
	let meta1;
	let meta1_content_value;

	return {
		c() {
			meta0 = element("meta");
			t = space();
			meta1 = element("meta");
			this.h();
		},
		l(nodes) {
			meta0 = claim_element(nodes, "META", { property: true, content: true });
			t = claim_space(nodes);
			meta1 = claim_element(nodes, "META", { name: true, content: true });
			this.h();
		},
		h() {
			attr(meta0, "property", "og:image");
			attr(meta0, "content", meta0_content_value = /*image*/ ctx[1].url);
			attr(meta1, "name", "twitter:image");
			attr(meta1, "content", meta1_content_value = /*image*/ ctx[1].url);
		},
		m(target, anchor) {
			insert_hydration(target, meta0, anchor);
			insert_hydration(target, t, anchor);
			insert_hydration(target, meta1, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*image*/ 2 && meta0_content_value !== (meta0_content_value = /*image*/ ctx[1].url)) {
				attr(meta0, "content", meta0_content_value);
			}

			if (dirty & /*image*/ 2 && meta1_content_value !== (meta1_content_value = /*image*/ ctx[1].url)) {
				attr(meta1, "content", meta1_content_value);
			}
		},
		d(detaching) {
			if (detaching) detach(meta0);
			if (detaching) detach(t);
			if (detaching) detach(meta1);
		}
	};
}

function create_fragment(ctx) {
	let link0;
	let link0_href_value;
	let link1;
	let link2;
	let link3;
	let title_value;
	let meta;
	let style;
	let t;
	document.title = title_value = /*title*/ ctx[2];
	let if_block = /*image*/ ctx[1].url && create_if_block(ctx);

	return {
		c() {
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			link3 = element("link");
			meta = element("meta");
			if (if_block) if_block.c();
			style = element("style");
			t = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: black;\n  --color-accent2: #999999;\n  --color-shade: #2d3339;\n\n  --inner-max-width: 800px;\n\n  /* Base values */\n  --box-shadow: 0px 2px 8px rgba(0, 0, 0, 0.1);\n  --border-radius: 2px;\n  --border-color: #e0e1e1;\n  --body-font: \"Merriweather\", serif;\n  --heading-font: \"Inter\", sans-serif;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: var(--heading-font);\n  color: #111;\n  line-height: 1.5;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1150px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: clamp(2rem, 10vw, 3rem);\n  line-height: 1.1;\n  font-weight: 600;\n  letter-spacing: -0.15rem;\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 1px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0; /* reset */\n  border-radius: 0.25rem;\n  font-size: 1rem;\n}\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-q47lvn', document.head);

			link0 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link2 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			link3 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			meta = claim_element(head_nodes, "META", { name: true, content: true });
			if (if_block) if_block.l(head_nodes);
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: black;\n  --color-accent2: #999999;\n  --color-shade: #2d3339;\n\n  --inner-max-width: 800px;\n\n  /* Base values */\n  --box-shadow: 0px 2px 8px rgba(0, 0, 0, 0.1);\n  --border-radius: 2px;\n  --border-color: #e0e1e1;\n  --body-font: \"Merriweather\", serif;\n  --heading-font: \"Inter\", sans-serif;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: var(--heading-font);\n  color: #111;\n  line-height: 1.5;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1150px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: clamp(2rem, 10vw, 3rem);\n  line-height: 1.1;\n  font-weight: 600;\n  letter-spacing: -0.15rem;\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 1px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0; /* reset */\n  border-radius: 0.25rem;\n  font-size: 1rem;\n}\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(link0, "rel", "shortcut icon");
			attr(link0, "type", "image/jpg");
			attr(link0, "sizes", "32x32");
			attr(link0, "href", link0_href_value = /*favicon*/ ctx[0].url);
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.bunny.net");
			attr(link2, "href", "https://fonts.bunny.net/css?family=inter:100,200,300,400,500,600,700,800,900");
			attr(link2, "rel", "stylesheet");
			attr(link3, "href", "https://fonts.bunny.net/css?family=merriweather:300,300i,400,400i,700,700i,900,900i");
			attr(link3, "rel", "stylesheet");
			attr(meta, "name", "description");
			attr(meta, "content", /*description*/ ctx[3]);
		},
		m(target, anchor) {
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, link3);
			append_hydration(document.head, meta);
			if (if_block) if_block.m(document.head, null);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link0_href_value !== (link0_href_value = /*favicon*/ ctx[0].url)) {
				attr(link0, "href", link0_href_value);
			}

			if (dirty & /*title*/ 4 && title_value !== (title_value = /*title*/ ctx[2])) {
				document.title = title_value;
			}

			if (dirty & /*description*/ 8) {
				attr(meta, "content", /*description*/ ctx[3]);
			}

			if (/*image*/ ctx[1].url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(style.parentNode, style);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(link0);
			detach(link1);
			detach(link2);
			detach(link3);
			detach(meta);
			if (if_block) if_block.d(detaching);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { image } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('image' in $$props) $$invalidate(1, image = $$props.image);
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('description' in $$props) $$invalidate(3, description = $$props.description);
	};

	return [favicon, image, title, description];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			favicon: 0,
			image: 1,
			title: 2,
			description: 3
		});
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block$1(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block$1(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[10] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[10] = list[i].link;
	return child_ctx;
}

// (108:31) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (106:6) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (113:6) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[10].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-hfomrx");
			attr(a, "href", a_href_value = /*link*/ ctx[10].url);
			toggle_class(a, "active", /*link*/ ctx[10].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[10].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[10].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*site_nav, window*/ 2) {
				toggle_class(a, "active", /*link*/ ctx[10].url === window.location.pathname);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (125:31) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (123:6) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (135:4) {#if mobileNavOpen}
function create_if_block$2(ctx) {
	let nav;
	let t;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-hfomrx");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-hfomrx");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[8]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (137:8) {#each site_nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[10].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[10].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[10].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[10].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div3;
	let div2;
	let header;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let div1;
	let a1;
	let t2;
	let button;
	let icon;
	let t3;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block2 = /*mobileNavOpen*/ ctx[2] && create_if_block$2(ctx);

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			header = element("header");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			div1 = element("div");
			a1 = element("a");
			if (if_block1) if_block1.c();
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t3 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a1 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			if (if_block1) if_block1.l(a1_nodes);
			a1_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-hfomrx");
			attr(nav, "class", "svelte-hfomrx");
			attr(div0, "class", "desktop-nav svelte-hfomrx");
			attr(a1, "href", "/");
			attr(a1, "class", "logo svelte-hfomrx");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-hfomrx");
			attr(header, "class", "section-container svelte-hfomrx");
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-754ef74e-5456-4c86-baa0-94f149ad78e9");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, header);
			append_hydration(header, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(header, t1);
			append_hydration(header, div1);
			append_hydration(div1, a1);
			if (if_block1) if_block1.m(a1, null);
			append_hydration(div1, t2);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t3);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*site_nav, window*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a1, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[2]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 4) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$2(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { image } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(2, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(2, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('image' in $$props) $$invalidate(4, image = $$props.image);
		if ('title' in $$props) $$invalidate(5, title = $$props.title);
		if ('description' in $$props) $$invalidate(6, description = $$props.description);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
	};

	return [
		logo,
		site_nav,
		mobileNavOpen,
		favicon,
		image,
		title,
		description,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			favicon: 3,
			image: 4,
			title: 5,
			description: 6,
			logo: 0,
			site_nav: 1
		});
	}
}

var global$1 = typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {};
function bind(fn, thisArg) {
  return function wrap() {
    return fn.apply(thisArg, arguments);
  };
}
const {toString} = Object.prototype;
const {getPrototypeOf} = Object;
const kindOf = ((cache) => (thing) => {
  const str = toString.call(thing);
  return cache[str] || (cache[str] = str.slice(8, -1).toLowerCase());
})(Object.create(null));
const kindOfTest = (type) => {
  type = type.toLowerCase();
  return (thing) => kindOf(thing) === type;
};
const typeOfTest = (type) => (thing) => typeof thing === type;
const {isArray} = Array;
const isUndefined = typeOfTest("undefined");
function isBuffer(val) {
  return val !== null && !isUndefined(val) && val.constructor !== null && !isUndefined(val.constructor) && isFunction(val.constructor.isBuffer) && val.constructor.isBuffer(val);
}
const isArrayBuffer = kindOfTest("ArrayBuffer");
function isArrayBufferView(val) {
  let result;
  if (typeof ArrayBuffer !== "undefined" && ArrayBuffer.isView) {
    result = ArrayBuffer.isView(val);
  } else {
    result = val && val.buffer && isArrayBuffer(val.buffer);
  }
  return result;
}
const isString = typeOfTest("string");
const isFunction = typeOfTest("function");
const isNumber = typeOfTest("number");
const isObject = (thing) => thing !== null && typeof thing === "object";
const isBoolean = (thing) => thing === true || thing === false;
const isPlainObject = (val) => {
  if (kindOf(val) !== "object") {
    return false;
  }
  const prototype = getPrototypeOf(val);
  return (prototype === null || prototype === Object.prototype || Object.getPrototypeOf(prototype) === null) && !(Symbol.toStringTag in val) && !(Symbol.iterator in val);
};
const isDate = kindOfTest("Date");
const isFile = kindOfTest("File");
const isBlob = kindOfTest("Blob");
const isFileList = kindOfTest("FileList");
const isStream = (val) => isObject(val) && isFunction(val.pipe);
const isFormData = (thing) => {
  let kind;
  return thing && (typeof FormData === "function" && thing instanceof FormData || isFunction(thing.append) && ((kind = kindOf(thing)) === "formdata" || kind === "object" && isFunction(thing.toString) && thing.toString() === "[object FormData]"));
};
const isURLSearchParams = kindOfTest("URLSearchParams");
const trim = (str) => str.trim ? str.trim() : str.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g, "");
function forEach(obj, fn, {allOwnKeys = false} = {}) {
  if (obj === null || typeof obj === "undefined") {
    return;
  }
  let i;
  let l;
  if (typeof obj !== "object") {
    obj = [obj];
  }
  if (isArray(obj)) {
    for (i = 0, l = obj.length; i < l; i++) {
      fn.call(null, obj[i], i, obj);
    }
  } else {
    const keys = allOwnKeys ? Object.getOwnPropertyNames(obj) : Object.keys(obj);
    const len = keys.length;
    let key;
    for (i = 0; i < len; i++) {
      key = keys[i];
      fn.call(null, obj[key], key, obj);
    }
  }
}
function findKey(obj, key) {
  key = key.toLowerCase();
  const keys = Object.keys(obj);
  let i = keys.length;
  let _key;
  while (i-- > 0) {
    _key = keys[i];
    if (key === _key.toLowerCase()) {
      return _key;
    }
  }
  return null;
}
const _global = (() => {
  if (typeof globalThis !== "undefined")
    return globalThis;
  return typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : global$1;
})();
const isContextDefined = (context) => !isUndefined(context) && context !== _global;
function merge() {
  const {caseless} = isContextDefined(this) && this || {};
  const result = {};
  const assignValue = (val, key) => {
    const targetKey = caseless && findKey(result, key) || key;
    if (isPlainObject(result[targetKey]) && isPlainObject(val)) {
      result[targetKey] = merge(result[targetKey], val);
    } else if (isPlainObject(val)) {
      result[targetKey] = merge({}, val);
    } else if (isArray(val)) {
      result[targetKey] = val.slice();
    } else {
      result[targetKey] = val;
    }
  };
  for (let i = 0, l = arguments.length; i < l; i++) {
    arguments[i] && forEach(arguments[i], assignValue);
  }
  return result;
}
const extend = (a, b, thisArg, {allOwnKeys} = {}) => {
  forEach(b, (val, key) => {
    if (thisArg && isFunction(val)) {
      a[key] = bind(val, thisArg);
    } else {
      a[key] = val;
    }
  }, {allOwnKeys});
  return a;
};
const stripBOM = (content) => {
  if (content.charCodeAt(0) === 65279) {
    content = content.slice(1);
  }
  return content;
};
const inherits = (constructor, superConstructor, props, descriptors) => {
  constructor.prototype = Object.create(superConstructor.prototype, descriptors);
  constructor.prototype.constructor = constructor;
  Object.defineProperty(constructor, "super", {
    value: superConstructor.prototype
  });
  props && Object.assign(constructor.prototype, props);
};
const toFlatObject = (sourceObj, destObj, filter, propFilter) => {
  let props;
  let i;
  let prop;
  const merged = {};
  destObj = destObj || {};
  if (sourceObj == null)
    return destObj;
  do {
    props = Object.getOwnPropertyNames(sourceObj);
    i = props.length;
    while (i-- > 0) {
      prop = props[i];
      if ((!propFilter || propFilter(prop, sourceObj, destObj)) && !merged[prop]) {
        destObj[prop] = sourceObj[prop];
        merged[prop] = true;
      }
    }
    sourceObj = filter !== false && getPrototypeOf(sourceObj);
  } while (sourceObj && (!filter || filter(sourceObj, destObj)) && sourceObj !== Object.prototype);
  return destObj;
};
const endsWith = (str, searchString, position) => {
  str = String(str);
  if (position === void 0 || position > str.length) {
    position = str.length;
  }
  position -= searchString.length;
  const lastIndex = str.indexOf(searchString, position);
  return lastIndex !== -1 && lastIndex === position;
};
const toArray = (thing) => {
  if (!thing)
    return null;
  if (isArray(thing))
    return thing;
  let i = thing.length;
  if (!isNumber(i))
    return null;
  const arr = new Array(i);
  while (i-- > 0) {
    arr[i] = thing[i];
  }
  return arr;
};
const isTypedArray = ((TypedArray) => {
  return (thing) => {
    return TypedArray && thing instanceof TypedArray;
  };
})(typeof Uint8Array !== "undefined" && getPrototypeOf(Uint8Array));
const forEachEntry = (obj, fn) => {
  const generator = obj && obj[Symbol.iterator];
  const iterator = generator.call(obj);
  let result;
  while ((result = iterator.next()) && !result.done) {
    const pair = result.value;
    fn.call(obj, pair[0], pair[1]);
  }
};
const matchAll = (regExp, str) => {
  let matches;
  const arr = [];
  while ((matches = regExp.exec(str)) !== null) {
    arr.push(matches);
  }
  return arr;
};
const isHTMLForm = kindOfTest("HTMLFormElement");
const toCamelCase = (str) => {
  return str.toLowerCase().replace(/[-_\s]([a-z\d])(\w*)/g, function replacer(m, p1, p2) {
    return p1.toUpperCase() + p2;
  });
};
const hasOwnProperty = (({hasOwnProperty: hasOwnProperty2}) => (obj, prop) => hasOwnProperty2.call(obj, prop))(Object.prototype);
const isRegExp = kindOfTest("RegExp");
const reduceDescriptors = (obj, reducer) => {
  const descriptors = Object.getOwnPropertyDescriptors(obj);
  const reducedDescriptors = {};
  forEach(descriptors, (descriptor, name) => {
    if (reducer(descriptor, name, obj) !== false) {
      reducedDescriptors[name] = descriptor;
    }
  });
  Object.defineProperties(obj, reducedDescriptors);
};
const freezeMethods = (obj) => {
  reduceDescriptors(obj, (descriptor, name) => {
    if (isFunction(obj) && ["arguments", "caller", "callee"].indexOf(name) !== -1) {
      return false;
    }
    const value = obj[name];
    if (!isFunction(value))
      return;
    descriptor.enumerable = false;
    if ("writable" in descriptor) {
      descriptor.writable = false;
      return;
    }
    if (!descriptor.set) {
      descriptor.set = () => {
        throw Error("Can not rewrite read-only method '" + name + "'");
      };
    }
  });
};
const toObjectSet = (arrayOrString, delimiter) => {
  const obj = {};
  const define = (arr) => {
    arr.forEach((value) => {
      obj[value] = true;
    });
  };
  isArray(arrayOrString) ? define(arrayOrString) : define(String(arrayOrString).split(delimiter));
  return obj;
};
const noop$1 = () => {
};
const toFiniteNumber = (value, defaultValue) => {
  value = +value;
  return Number.isFinite(value) ? value : defaultValue;
};
const ALPHA = "abcdefghijklmnopqrstuvwxyz";
const DIGIT = "0123456789";
const ALPHABET = {
  DIGIT,
  ALPHA,
  ALPHA_DIGIT: ALPHA + ALPHA.toUpperCase() + DIGIT
};
const generateString = (size = 16, alphabet = ALPHABET.ALPHA_DIGIT) => {
  let str = "";
  const {length} = alphabet;
  while (size--) {
    str += alphabet[Math.random() * length | 0];
  }
  return str;
};
function isSpecCompliantForm(thing) {
  return !!(thing && isFunction(thing.append) && thing[Symbol.toStringTag] === "FormData" && thing[Symbol.iterator]);
}
const toJSONObject = (obj) => {
  const stack = new Array(10);
  const visit = (source, i) => {
    if (isObject(source)) {
      if (stack.indexOf(source) >= 0) {
        return;
      }
      if (!("toJSON" in source)) {
        stack[i] = source;
        const target = isArray(source) ? [] : {};
        forEach(source, (value, key) => {
          const reducedValue = visit(value, i + 1);
          !isUndefined(reducedValue) && (target[key] = reducedValue);
        });
        stack[i] = void 0;
        return target;
      }
    }
    return source;
  };
  return visit(obj, 0);
};
const isAsyncFn = kindOfTest("AsyncFunction");
const isThenable = (thing) => thing && (isObject(thing) || isFunction(thing)) && isFunction(thing.then) && isFunction(thing.catch);
var utils = {
  isArray,
  isArrayBuffer,
  isBuffer,
  isFormData,
  isArrayBufferView,
  isString,
  isNumber,
  isBoolean,
  isObject,
  isPlainObject,
  isUndefined,
  isDate,
  isFile,
  isBlob,
  isRegExp,
  isFunction,
  isStream,
  isURLSearchParams,
  isTypedArray,
  isFileList,
  forEach,
  merge,
  extend,
  trim,
  stripBOM,
  inherits,
  toFlatObject,
  kindOf,
  kindOfTest,
  endsWith,
  toArray,
  forEachEntry,
  matchAll,
  isHTMLForm,
  hasOwnProperty,
  hasOwnProp: hasOwnProperty,
  reduceDescriptors,
  freezeMethods,
  toObjectSet,
  toCamelCase,
  noop: noop$1,
  toFiniteNumber,
  findKey,
  global: _global,
  isContextDefined,
  ALPHABET,
  generateString,
  isSpecCompliantForm,
  toJSONObject,
  isAsyncFn,
  isThenable
};

function AxiosError(message, code, config, request, response) {
  Error.call(this);
  if (Error.captureStackTrace) {
    Error.captureStackTrace(this, this.constructor);
  } else {
    this.stack = new Error().stack;
  }
  this.message = message;
  this.name = "AxiosError";
  code && (this.code = code);
  config && (this.config = config);
  request && (this.request = request);
  response && (this.response = response);
}
utils.inherits(AxiosError, Error, {
  toJSON: function toJSON() {
    return {
      message: this.message,
      name: this.name,
      description: this.description,
      number: this.number,
      fileName: this.fileName,
      lineNumber: this.lineNumber,
      columnNumber: this.columnNumber,
      stack: this.stack,
      config: utils.toJSONObject(this.config),
      code: this.code,
      status: this.response && this.response.status ? this.response.status : null
    };
  }
});
const prototype = AxiosError.prototype;
const descriptors = {};
[
  "ERR_BAD_OPTION_VALUE",
  "ERR_BAD_OPTION",
  "ECONNABORTED",
  "ETIMEDOUT",
  "ERR_NETWORK",
  "ERR_FR_TOO_MANY_REDIRECTS",
  "ERR_DEPRECATED",
  "ERR_BAD_RESPONSE",
  "ERR_BAD_REQUEST",
  "ERR_CANCELED",
  "ERR_NOT_SUPPORT",
  "ERR_INVALID_URL"
].forEach((code) => {
  descriptors[code] = {value: code};
});
Object.defineProperties(AxiosError, descriptors);
Object.defineProperty(prototype, "isAxiosError", {value: true});
AxiosError.from = (error, code, config, request, response, customProps) => {
  const axiosError = Object.create(prototype);
  utils.toFlatObject(error, axiosError, function filter(obj) {
    return obj !== Error.prototype;
  }, (prop) => {
    return prop !== "isAxiosError";
  });
  AxiosError.call(axiosError, error.message, code, config, request, response);
  axiosError.cause = error;
  axiosError.name = error.name;
  customProps && Object.assign(axiosError, customProps);
  return axiosError;
};

var lookup = [];
var revLookup = [];
var Arr = typeof Uint8Array !== "undefined" ? Uint8Array : Array;
var inited = false;
function init$1() {
  inited = true;
  var code = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  for (var i = 0, len = code.length; i < len; ++i) {
    lookup[i] = code[i];
    revLookup[code.charCodeAt(i)] = i;
  }
  revLookup["-".charCodeAt(0)] = 62;
  revLookup["_".charCodeAt(0)] = 63;
}
function toByteArray(b64) {
  if (!inited) {
    init$1();
  }
  var i, j, l, tmp, placeHolders, arr;
  var len = b64.length;
  if (len % 4 > 0) {
    throw new Error("Invalid string. Length must be a multiple of 4");
  }
  placeHolders = b64[len - 2] === "=" ? 2 : b64[len - 1] === "=" ? 1 : 0;
  arr = new Arr(len * 3 / 4 - placeHolders);
  l = placeHolders > 0 ? len - 4 : len;
  var L = 0;
  for (i = 0, j = 0; i < l; i += 4, j += 3) {
    tmp = revLookup[b64.charCodeAt(i)] << 18 | revLookup[b64.charCodeAt(i + 1)] << 12 | revLookup[b64.charCodeAt(i + 2)] << 6 | revLookup[b64.charCodeAt(i + 3)];
    arr[L++] = tmp >> 16 & 255;
    arr[L++] = tmp >> 8 & 255;
    arr[L++] = tmp & 255;
  }
  if (placeHolders === 2) {
    tmp = revLookup[b64.charCodeAt(i)] << 2 | revLookup[b64.charCodeAt(i + 1)] >> 4;
    arr[L++] = tmp & 255;
  } else if (placeHolders === 1) {
    tmp = revLookup[b64.charCodeAt(i)] << 10 | revLookup[b64.charCodeAt(i + 1)] << 4 | revLookup[b64.charCodeAt(i + 2)] >> 2;
    arr[L++] = tmp >> 8 & 255;
    arr[L++] = tmp & 255;
  }
  return arr;
}
function tripletToBase64(num) {
  return lookup[num >> 18 & 63] + lookup[num >> 12 & 63] + lookup[num >> 6 & 63] + lookup[num & 63];
}
function encodeChunk(uint8, start, end) {
  var tmp;
  var output = [];
  for (var i = start; i < end; i += 3) {
    tmp = (uint8[i] << 16) + (uint8[i + 1] << 8) + uint8[i + 2];
    output.push(tripletToBase64(tmp));
  }
  return output.join("");
}
function fromByteArray(uint8) {
  if (!inited) {
    init$1();
  }
  var tmp;
  var len = uint8.length;
  var extraBytes = len % 3;
  var output = "";
  var parts = [];
  var maxChunkLength = 16383;
  for (var i = 0, len2 = len - extraBytes; i < len2; i += maxChunkLength) {
    parts.push(encodeChunk(uint8, i, i + maxChunkLength > len2 ? len2 : i + maxChunkLength));
  }
  if (extraBytes === 1) {
    tmp = uint8[len - 1];
    output += lookup[tmp >> 2];
    output += lookup[tmp << 4 & 63];
    output += "==";
  } else if (extraBytes === 2) {
    tmp = (uint8[len - 2] << 8) + uint8[len - 1];
    output += lookup[tmp >> 10];
    output += lookup[tmp >> 4 & 63];
    output += lookup[tmp << 2 & 63];
    output += "=";
  }
  parts.push(output);
  return parts.join("");
}
function read(buffer, offset, isLE, mLen, nBytes) {
  var e, m;
  var eLen = nBytes * 8 - mLen - 1;
  var eMax = (1 << eLen) - 1;
  var eBias = eMax >> 1;
  var nBits = -7;
  var i = isLE ? nBytes - 1 : 0;
  var d = isLE ? -1 : 1;
  var s = buffer[offset + i];
  i += d;
  e = s & (1 << -nBits) - 1;
  s >>= -nBits;
  nBits += eLen;
  for (; nBits > 0; e = e * 256 + buffer[offset + i], i += d, nBits -= 8) {
  }
  m = e & (1 << -nBits) - 1;
  e >>= -nBits;
  nBits += mLen;
  for (; nBits > 0; m = m * 256 + buffer[offset + i], i += d, nBits -= 8) {
  }
  if (e === 0) {
    e = 1 - eBias;
  } else if (e === eMax) {
    return m ? NaN : (s ? -1 : 1) * Infinity;
  } else {
    m = m + Math.pow(2, mLen);
    e = e - eBias;
  }
  return (s ? -1 : 1) * m * Math.pow(2, e - mLen);
}
function write(buffer, value, offset, isLE, mLen, nBytes) {
  var e, m, c;
  var eLen = nBytes * 8 - mLen - 1;
  var eMax = (1 << eLen) - 1;
  var eBias = eMax >> 1;
  var rt = mLen === 23 ? Math.pow(2, -24) - Math.pow(2, -77) : 0;
  var i = isLE ? 0 : nBytes - 1;
  var d = isLE ? 1 : -1;
  var s = value < 0 || value === 0 && 1 / value < 0 ? 1 : 0;
  value = Math.abs(value);
  if (isNaN(value) || value === Infinity) {
    m = isNaN(value) ? 1 : 0;
    e = eMax;
  } else {
    e = Math.floor(Math.log(value) / Math.LN2);
    if (value * (c = Math.pow(2, -e)) < 1) {
      e--;
      c *= 2;
    }
    if (e + eBias >= 1) {
      value += rt / c;
    } else {
      value += rt * Math.pow(2, 1 - eBias);
    }
    if (value * c >= 2) {
      e++;
      c /= 2;
    }
    if (e + eBias >= eMax) {
      m = 0;
      e = eMax;
    } else if (e + eBias >= 1) {
      m = (value * c - 1) * Math.pow(2, mLen);
      e = e + eBias;
    } else {
      m = value * Math.pow(2, eBias - 1) * Math.pow(2, mLen);
      e = 0;
    }
  }
  for (; mLen >= 8; buffer[offset + i] = m & 255, i += d, m /= 256, mLen -= 8) {
  }
  e = e << mLen | m;
  eLen += mLen;
  for (; eLen > 0; buffer[offset + i] = e & 255, i += d, e /= 256, eLen -= 8) {
  }
  buffer[offset + i - d] |= s * 128;
}
var toString$1 = {}.toString;
var isArray$1 = Array.isArray || function(arr) {
  return toString$1.call(arr) == "[object Array]";
};
/*!
 * The buffer module from node.js, for the browser.
 *
 * @author   Feross Aboukhadijeh <feross@feross.org> <http://feross.org>
 * @license  MIT
 */
var INSPECT_MAX_BYTES = 50;
Buffer.TYPED_ARRAY_SUPPORT = global$1.TYPED_ARRAY_SUPPORT !== void 0 ? global$1.TYPED_ARRAY_SUPPORT : true;
function kMaxLength() {
  return Buffer.TYPED_ARRAY_SUPPORT ? 2147483647 : 1073741823;
}
function createBuffer(that, length) {
  if (kMaxLength() < length) {
    throw new RangeError("Invalid typed array length");
  }
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    that = new Uint8Array(length);
    that.__proto__ = Buffer.prototype;
  } else {
    if (that === null) {
      that = new Buffer(length);
    }
    that.length = length;
  }
  return that;
}
function Buffer(arg, encodingOrOffset, length) {
  if (!Buffer.TYPED_ARRAY_SUPPORT && !(this instanceof Buffer)) {
    return new Buffer(arg, encodingOrOffset, length);
  }
  if (typeof arg === "number") {
    if (typeof encodingOrOffset === "string") {
      throw new Error("If encoding is specified then the first argument must be a string");
    }
    return allocUnsafe(this, arg);
  }
  return from(this, arg, encodingOrOffset, length);
}
Buffer.poolSize = 8192;
Buffer._augment = function(arr) {
  arr.__proto__ = Buffer.prototype;
  return arr;
};
function from(that, value, encodingOrOffset, length) {
  if (typeof value === "number") {
    throw new TypeError('"value" argument must not be a number');
  }
  if (typeof ArrayBuffer !== "undefined" && value instanceof ArrayBuffer) {
    return fromArrayBuffer(that, value, encodingOrOffset, length);
  }
  if (typeof value === "string") {
    return fromString(that, value, encodingOrOffset);
  }
  return fromObject(that, value);
}
Buffer.from = function(value, encodingOrOffset, length) {
  return from(null, value, encodingOrOffset, length);
};
if (Buffer.TYPED_ARRAY_SUPPORT) {
  Buffer.prototype.__proto__ = Uint8Array.prototype;
  Buffer.__proto__ = Uint8Array;
}
function assertSize(size) {
  if (typeof size !== "number") {
    throw new TypeError('"size" argument must be a number');
  } else if (size < 0) {
    throw new RangeError('"size" argument must not be negative');
  }
}
function alloc(that, size, fill2, encoding) {
  assertSize(size);
  if (size <= 0) {
    return createBuffer(that, size);
  }
  if (fill2 !== void 0) {
    return typeof encoding === "string" ? createBuffer(that, size).fill(fill2, encoding) : createBuffer(that, size).fill(fill2);
  }
  return createBuffer(that, size);
}
Buffer.alloc = function(size, fill2, encoding) {
  return alloc(null, size, fill2, encoding);
};
function allocUnsafe(that, size) {
  assertSize(size);
  that = createBuffer(that, size < 0 ? 0 : checked(size) | 0);
  if (!Buffer.TYPED_ARRAY_SUPPORT) {
    for (var i = 0; i < size; ++i) {
      that[i] = 0;
    }
  }
  return that;
}
Buffer.allocUnsafe = function(size) {
  return allocUnsafe(null, size);
};
Buffer.allocUnsafeSlow = function(size) {
  return allocUnsafe(null, size);
};
function fromString(that, string, encoding) {
  if (typeof encoding !== "string" || encoding === "") {
    encoding = "utf8";
  }
  if (!Buffer.isEncoding(encoding)) {
    throw new TypeError('"encoding" must be a valid string encoding');
  }
  var length = byteLength(string, encoding) | 0;
  that = createBuffer(that, length);
  var actual = that.write(string, encoding);
  if (actual !== length) {
    that = that.slice(0, actual);
  }
  return that;
}
function fromArrayLike(that, array) {
  var length = array.length < 0 ? 0 : checked(array.length) | 0;
  that = createBuffer(that, length);
  for (var i = 0; i < length; i += 1) {
    that[i] = array[i] & 255;
  }
  return that;
}
function fromArrayBuffer(that, array, byteOffset, length) {
  array.byteLength;
  if (byteOffset < 0 || array.byteLength < byteOffset) {
    throw new RangeError("'offset' is out of bounds");
  }
  if (array.byteLength < byteOffset + (length || 0)) {
    throw new RangeError("'length' is out of bounds");
  }
  if (byteOffset === void 0 && length === void 0) {
    array = new Uint8Array(array);
  } else if (length === void 0) {
    array = new Uint8Array(array, byteOffset);
  } else {
    array = new Uint8Array(array, byteOffset, length);
  }
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    that = array;
    that.__proto__ = Buffer.prototype;
  } else {
    that = fromArrayLike(that, array);
  }
  return that;
}
function fromObject(that, obj) {
  if (internalIsBuffer(obj)) {
    var len = checked(obj.length) | 0;
    that = createBuffer(that, len);
    if (that.length === 0) {
      return that;
    }
    obj.copy(that, 0, 0, len);
    return that;
  }
  if (obj) {
    if (typeof ArrayBuffer !== "undefined" && obj.buffer instanceof ArrayBuffer || "length" in obj) {
      if (typeof obj.length !== "number" || isnan(obj.length)) {
        return createBuffer(that, 0);
      }
      return fromArrayLike(that, obj);
    }
    if (obj.type === "Buffer" && isArray$1(obj.data)) {
      return fromArrayLike(that, obj.data);
    }
  }
  throw new TypeError("First argument must be a string, Buffer, ArrayBuffer, Array, or array-like object.");
}
function checked(length) {
  if (length >= kMaxLength()) {
    throw new RangeError("Attempt to allocate Buffer larger than maximum size: 0x" + kMaxLength().toString(16) + " bytes");
  }
  return length | 0;
}
Buffer.isBuffer = isBuffer$1;
function internalIsBuffer(b) {
  return !!(b != null && b._isBuffer);
}
Buffer.compare = function compare(a, b) {
  if (!internalIsBuffer(a) || !internalIsBuffer(b)) {
    throw new TypeError("Arguments must be Buffers");
  }
  if (a === b)
    return 0;
  var x = a.length;
  var y = b.length;
  for (var i = 0, len = Math.min(x, y); i < len; ++i) {
    if (a[i] !== b[i]) {
      x = a[i];
      y = b[i];
      break;
    }
  }
  if (x < y)
    return -1;
  if (y < x)
    return 1;
  return 0;
};
Buffer.isEncoding = function isEncoding(encoding) {
  switch (String(encoding).toLowerCase()) {
    case "hex":
    case "utf8":
    case "utf-8":
    case "ascii":
    case "latin1":
    case "binary":
    case "base64":
    case "ucs2":
    case "ucs-2":
    case "utf16le":
    case "utf-16le":
      return true;
    default:
      return false;
  }
};
Buffer.concat = function concat(list, length) {
  if (!isArray$1(list)) {
    throw new TypeError('"list" argument must be an Array of Buffers');
  }
  if (list.length === 0) {
    return Buffer.alloc(0);
  }
  var i;
  if (length === void 0) {
    length = 0;
    for (i = 0; i < list.length; ++i) {
      length += list[i].length;
    }
  }
  var buffer = Buffer.allocUnsafe(length);
  var pos = 0;
  for (i = 0; i < list.length; ++i) {
    var buf = list[i];
    if (!internalIsBuffer(buf)) {
      throw new TypeError('"list" argument must be an Array of Buffers');
    }
    buf.copy(buffer, pos);
    pos += buf.length;
  }
  return buffer;
};
function byteLength(string, encoding) {
  if (internalIsBuffer(string)) {
    return string.length;
  }
  if (typeof ArrayBuffer !== "undefined" && typeof ArrayBuffer.isView === "function" && (ArrayBuffer.isView(string) || string instanceof ArrayBuffer)) {
    return string.byteLength;
  }
  if (typeof string !== "string") {
    string = "" + string;
  }
  var len = string.length;
  if (len === 0)
    return 0;
  var loweredCase = false;
  for (; ; ) {
    switch (encoding) {
      case "ascii":
      case "latin1":
      case "binary":
        return len;
      case "utf8":
      case "utf-8":
      case void 0:
        return utf8ToBytes(string).length;
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return len * 2;
      case "hex":
        return len >>> 1;
      case "base64":
        return base64ToBytes(string).length;
      default:
        if (loweredCase)
          return utf8ToBytes(string).length;
        encoding = ("" + encoding).toLowerCase();
        loweredCase = true;
    }
  }
}
Buffer.byteLength = byteLength;
function slowToString(encoding, start, end) {
  var loweredCase = false;
  if (start === void 0 || start < 0) {
    start = 0;
  }
  if (start > this.length) {
    return "";
  }
  if (end === void 0 || end > this.length) {
    end = this.length;
  }
  if (end <= 0) {
    return "";
  }
  end >>>= 0;
  start >>>= 0;
  if (end <= start) {
    return "";
  }
  if (!encoding)
    encoding = "utf8";
  while (true) {
    switch (encoding) {
      case "hex":
        return hexSlice(this, start, end);
      case "utf8":
      case "utf-8":
        return utf8Slice(this, start, end);
      case "ascii":
        return asciiSlice(this, start, end);
      case "latin1":
      case "binary":
        return latin1Slice(this, start, end);
      case "base64":
        return base64Slice(this, start, end);
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return utf16leSlice(this, start, end);
      default:
        if (loweredCase)
          throw new TypeError("Unknown encoding: " + encoding);
        encoding = (encoding + "").toLowerCase();
        loweredCase = true;
    }
  }
}
Buffer.prototype._isBuffer = true;
function swap(b, n, m) {
  var i = b[n];
  b[n] = b[m];
  b[m] = i;
}
Buffer.prototype.swap16 = function swap16() {
  var len = this.length;
  if (len % 2 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 16-bits");
  }
  for (var i = 0; i < len; i += 2) {
    swap(this, i, i + 1);
  }
  return this;
};
Buffer.prototype.swap32 = function swap32() {
  var len = this.length;
  if (len % 4 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 32-bits");
  }
  for (var i = 0; i < len; i += 4) {
    swap(this, i, i + 3);
    swap(this, i + 1, i + 2);
  }
  return this;
};
Buffer.prototype.swap64 = function swap64() {
  var len = this.length;
  if (len % 8 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 64-bits");
  }
  for (var i = 0; i < len; i += 8) {
    swap(this, i, i + 7);
    swap(this, i + 1, i + 6);
    swap(this, i + 2, i + 5);
    swap(this, i + 3, i + 4);
  }
  return this;
};
Buffer.prototype.toString = function toString2() {
  var length = this.length | 0;
  if (length === 0)
    return "";
  if (arguments.length === 0)
    return utf8Slice(this, 0, length);
  return slowToString.apply(this, arguments);
};
Buffer.prototype.equals = function equals(b) {
  if (!internalIsBuffer(b))
    throw new TypeError("Argument must be a Buffer");
  if (this === b)
    return true;
  return Buffer.compare(this, b) === 0;
};
Buffer.prototype.inspect = function inspect() {
  var str = "";
  var max = INSPECT_MAX_BYTES;
  if (this.length > 0) {
    str = this.toString("hex", 0, max).match(/.{2}/g).join(" ");
    if (this.length > max)
      str += " ... ";
  }
  return "<Buffer " + str + ">";
};
Buffer.prototype.compare = function compare2(target, start, end, thisStart, thisEnd) {
  if (!internalIsBuffer(target)) {
    throw new TypeError("Argument must be a Buffer");
  }
  if (start === void 0) {
    start = 0;
  }
  if (end === void 0) {
    end = target ? target.length : 0;
  }
  if (thisStart === void 0) {
    thisStart = 0;
  }
  if (thisEnd === void 0) {
    thisEnd = this.length;
  }
  if (start < 0 || end > target.length || thisStart < 0 || thisEnd > this.length) {
    throw new RangeError("out of range index");
  }
  if (thisStart >= thisEnd && start >= end) {
    return 0;
  }
  if (thisStart >= thisEnd) {
    return -1;
  }
  if (start >= end) {
    return 1;
  }
  start >>>= 0;
  end >>>= 0;
  thisStart >>>= 0;
  thisEnd >>>= 0;
  if (this === target)
    return 0;
  var x = thisEnd - thisStart;
  var y = end - start;
  var len = Math.min(x, y);
  var thisCopy = this.slice(thisStart, thisEnd);
  var targetCopy = target.slice(start, end);
  for (var i = 0; i < len; ++i) {
    if (thisCopy[i] !== targetCopy[i]) {
      x = thisCopy[i];
      y = targetCopy[i];
      break;
    }
  }
  if (x < y)
    return -1;
  if (y < x)
    return 1;
  return 0;
};
function bidirectionalIndexOf(buffer, val, byteOffset, encoding, dir) {
  if (buffer.length === 0)
    return -1;
  if (typeof byteOffset === "string") {
    encoding = byteOffset;
    byteOffset = 0;
  } else if (byteOffset > 2147483647) {
    byteOffset = 2147483647;
  } else if (byteOffset < -2147483648) {
    byteOffset = -2147483648;
  }
  byteOffset = +byteOffset;
  if (isNaN(byteOffset)) {
    byteOffset = dir ? 0 : buffer.length - 1;
  }
  if (byteOffset < 0)
    byteOffset = buffer.length + byteOffset;
  if (byteOffset >= buffer.length) {
    if (dir)
      return -1;
    else
      byteOffset = buffer.length - 1;
  } else if (byteOffset < 0) {
    if (dir)
      byteOffset = 0;
    else
      return -1;
  }
  if (typeof val === "string") {
    val = Buffer.from(val, encoding);
  }
  if (internalIsBuffer(val)) {
    if (val.length === 0) {
      return -1;
    }
    return arrayIndexOf(buffer, val, byteOffset, encoding, dir);
  } else if (typeof val === "number") {
    val = val & 255;
    if (Buffer.TYPED_ARRAY_SUPPORT && typeof Uint8Array.prototype.indexOf === "function") {
      if (dir) {
        return Uint8Array.prototype.indexOf.call(buffer, val, byteOffset);
      } else {
        return Uint8Array.prototype.lastIndexOf.call(buffer, val, byteOffset);
      }
    }
    return arrayIndexOf(buffer, [val], byteOffset, encoding, dir);
  }
  throw new TypeError("val must be string, number or Buffer");
}
function arrayIndexOf(arr, val, byteOffset, encoding, dir) {
  var indexSize = 1;
  var arrLength = arr.length;
  var valLength = val.length;
  if (encoding !== void 0) {
    encoding = String(encoding).toLowerCase();
    if (encoding === "ucs2" || encoding === "ucs-2" || encoding === "utf16le" || encoding === "utf-16le") {
      if (arr.length < 2 || val.length < 2) {
        return -1;
      }
      indexSize = 2;
      arrLength /= 2;
      valLength /= 2;
      byteOffset /= 2;
    }
  }
  function read2(buf, i2) {
    if (indexSize === 1) {
      return buf[i2];
    } else {
      return buf.readUInt16BE(i2 * indexSize);
    }
  }
  var i;
  if (dir) {
    var foundIndex = -1;
    for (i = byteOffset; i < arrLength; i++) {
      if (read2(arr, i) === read2(val, foundIndex === -1 ? 0 : i - foundIndex)) {
        if (foundIndex === -1)
          foundIndex = i;
        if (i - foundIndex + 1 === valLength)
          return foundIndex * indexSize;
      } else {
        if (foundIndex !== -1)
          i -= i - foundIndex;
        foundIndex = -1;
      }
    }
  } else {
    if (byteOffset + valLength > arrLength)
      byteOffset = arrLength - valLength;
    for (i = byteOffset; i >= 0; i--) {
      var found = true;
      for (var j = 0; j < valLength; j++) {
        if (read2(arr, i + j) !== read2(val, j)) {
          found = false;
          break;
        }
      }
      if (found)
        return i;
    }
  }
  return -1;
}
Buffer.prototype.includes = function includes(val, byteOffset, encoding) {
  return this.indexOf(val, byteOffset, encoding) !== -1;
};
Buffer.prototype.indexOf = function indexOf(val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, true);
};
Buffer.prototype.lastIndexOf = function lastIndexOf(val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, false);
};
function hexWrite(buf, string, offset, length) {
  offset = Number(offset) || 0;
  var remaining = buf.length - offset;
  if (!length) {
    length = remaining;
  } else {
    length = Number(length);
    if (length > remaining) {
      length = remaining;
    }
  }
  var strLen = string.length;
  if (strLen % 2 !== 0)
    throw new TypeError("Invalid hex string");
  if (length > strLen / 2) {
    length = strLen / 2;
  }
  for (var i = 0; i < length; ++i) {
    var parsed = parseInt(string.substr(i * 2, 2), 16);
    if (isNaN(parsed))
      return i;
    buf[offset + i] = parsed;
  }
  return i;
}
function utf8Write(buf, string, offset, length) {
  return blitBuffer(utf8ToBytes(string, buf.length - offset), buf, offset, length);
}
function asciiWrite(buf, string, offset, length) {
  return blitBuffer(asciiToBytes(string), buf, offset, length);
}
function latin1Write(buf, string, offset, length) {
  return asciiWrite(buf, string, offset, length);
}
function base64Write(buf, string, offset, length) {
  return blitBuffer(base64ToBytes(string), buf, offset, length);
}
function ucs2Write(buf, string, offset, length) {
  return blitBuffer(utf16leToBytes(string, buf.length - offset), buf, offset, length);
}
Buffer.prototype.write = function write2(string, offset, length, encoding) {
  if (offset === void 0) {
    encoding = "utf8";
    length = this.length;
    offset = 0;
  } else if (length === void 0 && typeof offset === "string") {
    encoding = offset;
    length = this.length;
    offset = 0;
  } else if (isFinite(offset)) {
    offset = offset | 0;
    if (isFinite(length)) {
      length = length | 0;
      if (encoding === void 0)
        encoding = "utf8";
    } else {
      encoding = length;
      length = void 0;
    }
  } else {
    throw new Error("Buffer.write(string, encoding, offset[, length]) is no longer supported");
  }
  var remaining = this.length - offset;
  if (length === void 0 || length > remaining)
    length = remaining;
  if (string.length > 0 && (length < 0 || offset < 0) || offset > this.length) {
    throw new RangeError("Attempt to write outside buffer bounds");
  }
  if (!encoding)
    encoding = "utf8";
  var loweredCase = false;
  for (; ; ) {
    switch (encoding) {
      case "hex":
        return hexWrite(this, string, offset, length);
      case "utf8":
      case "utf-8":
        return utf8Write(this, string, offset, length);
      case "ascii":
        return asciiWrite(this, string, offset, length);
      case "latin1":
      case "binary":
        return latin1Write(this, string, offset, length);
      case "base64":
        return base64Write(this, string, offset, length);
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return ucs2Write(this, string, offset, length);
      default:
        if (loweredCase)
          throw new TypeError("Unknown encoding: " + encoding);
        encoding = ("" + encoding).toLowerCase();
        loweredCase = true;
    }
  }
};
Buffer.prototype.toJSON = function toJSON() {
  return {
    type: "Buffer",
    data: Array.prototype.slice.call(this._arr || this, 0)
  };
};
function base64Slice(buf, start, end) {
  if (start === 0 && end === buf.length) {
    return fromByteArray(buf);
  } else {
    return fromByteArray(buf.slice(start, end));
  }
}
function utf8Slice(buf, start, end) {
  end = Math.min(buf.length, end);
  var res = [];
  var i = start;
  while (i < end) {
    var firstByte = buf[i];
    var codePoint = null;
    var bytesPerSequence = firstByte > 239 ? 4 : firstByte > 223 ? 3 : firstByte > 191 ? 2 : 1;
    if (i + bytesPerSequence <= end) {
      var secondByte, thirdByte, fourthByte, tempCodePoint;
      switch (bytesPerSequence) {
        case 1:
          if (firstByte < 128) {
            codePoint = firstByte;
          }
          break;
        case 2:
          secondByte = buf[i + 1];
          if ((secondByte & 192) === 128) {
            tempCodePoint = (firstByte & 31) << 6 | secondByte & 63;
            if (tempCodePoint > 127) {
              codePoint = tempCodePoint;
            }
          }
          break;
        case 3:
          secondByte = buf[i + 1];
          thirdByte = buf[i + 2];
          if ((secondByte & 192) === 128 && (thirdByte & 192) === 128) {
            tempCodePoint = (firstByte & 15) << 12 | (secondByte & 63) << 6 | thirdByte & 63;
            if (tempCodePoint > 2047 && (tempCodePoint < 55296 || tempCodePoint > 57343)) {
              codePoint = tempCodePoint;
            }
          }
          break;
        case 4:
          secondByte = buf[i + 1];
          thirdByte = buf[i + 2];
          fourthByte = buf[i + 3];
          if ((secondByte & 192) === 128 && (thirdByte & 192) === 128 && (fourthByte & 192) === 128) {
            tempCodePoint = (firstByte & 15) << 18 | (secondByte & 63) << 12 | (thirdByte & 63) << 6 | fourthByte & 63;
            if (tempCodePoint > 65535 && tempCodePoint < 1114112) {
              codePoint = tempCodePoint;
            }
          }
      }
    }
    if (codePoint === null) {
      codePoint = 65533;
      bytesPerSequence = 1;
    } else if (codePoint > 65535) {
      codePoint -= 65536;
      res.push(codePoint >>> 10 & 1023 | 55296);
      codePoint = 56320 | codePoint & 1023;
    }
    res.push(codePoint);
    i += bytesPerSequence;
  }
  return decodeCodePointsArray(res);
}
var MAX_ARGUMENTS_LENGTH = 4096;
function decodeCodePointsArray(codePoints) {
  var len = codePoints.length;
  if (len <= MAX_ARGUMENTS_LENGTH) {
    return String.fromCharCode.apply(String, codePoints);
  }
  var res = "";
  var i = 0;
  while (i < len) {
    res += String.fromCharCode.apply(String, codePoints.slice(i, i += MAX_ARGUMENTS_LENGTH));
  }
  return res;
}
function asciiSlice(buf, start, end) {
  var ret = "";
  end = Math.min(buf.length, end);
  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i] & 127);
  }
  return ret;
}
function latin1Slice(buf, start, end) {
  var ret = "";
  end = Math.min(buf.length, end);
  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i]);
  }
  return ret;
}
function hexSlice(buf, start, end) {
  var len = buf.length;
  if (!start || start < 0)
    start = 0;
  if (!end || end < 0 || end > len)
    end = len;
  var out = "";
  for (var i = start; i < end; ++i) {
    out += toHex(buf[i]);
  }
  return out;
}
function utf16leSlice(buf, start, end) {
  var bytes = buf.slice(start, end);
  var res = "";
  for (var i = 0; i < bytes.length; i += 2) {
    res += String.fromCharCode(bytes[i] + bytes[i + 1] * 256);
  }
  return res;
}
Buffer.prototype.slice = function slice(start, end) {
  var len = this.length;
  start = ~~start;
  end = end === void 0 ? len : ~~end;
  if (start < 0) {
    start += len;
    if (start < 0)
      start = 0;
  } else if (start > len) {
    start = len;
  }
  if (end < 0) {
    end += len;
    if (end < 0)
      end = 0;
  } else if (end > len) {
    end = len;
  }
  if (end < start)
    end = start;
  var newBuf;
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    newBuf = this.subarray(start, end);
    newBuf.__proto__ = Buffer.prototype;
  } else {
    var sliceLen = end - start;
    newBuf = new Buffer(sliceLen, void 0);
    for (var i = 0; i < sliceLen; ++i) {
      newBuf[i] = this[i + start];
    }
  }
  return newBuf;
};
function checkOffset(offset, ext, length) {
  if (offset % 1 !== 0 || offset < 0)
    throw new RangeError("offset is not uint");
  if (offset + ext > length)
    throw new RangeError("Trying to access beyond buffer length");
}
Buffer.prototype.readUIntLE = function readUIntLE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var val = this[offset];
  var mul = 1;
  var i = 0;
  while (++i < byteLength2 && (mul *= 256)) {
    val += this[offset + i] * mul;
  }
  return val;
};
Buffer.prototype.readUIntBE = function readUIntBE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    checkOffset(offset, byteLength2, this.length);
  }
  var val = this[offset + --byteLength2];
  var mul = 1;
  while (byteLength2 > 0 && (mul *= 256)) {
    val += this[offset + --byteLength2] * mul;
  }
  return val;
};
Buffer.prototype.readUInt8 = function readUInt8(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 1, this.length);
  return this[offset];
};
Buffer.prototype.readUInt16LE = function readUInt16LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  return this[offset] | this[offset + 1] << 8;
};
Buffer.prototype.readUInt16BE = function readUInt16BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  return this[offset] << 8 | this[offset + 1];
};
Buffer.prototype.readUInt32LE = function readUInt32LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return (this[offset] | this[offset + 1] << 8 | this[offset + 2] << 16) + this[offset + 3] * 16777216;
};
Buffer.prototype.readUInt32BE = function readUInt32BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] * 16777216 + (this[offset + 1] << 16 | this[offset + 2] << 8 | this[offset + 3]);
};
Buffer.prototype.readIntLE = function readIntLE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var val = this[offset];
  var mul = 1;
  var i = 0;
  while (++i < byteLength2 && (mul *= 256)) {
    val += this[offset + i] * mul;
  }
  mul *= 128;
  if (val >= mul)
    val -= Math.pow(2, 8 * byteLength2);
  return val;
};
Buffer.prototype.readIntBE = function readIntBE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var i = byteLength2;
  var mul = 1;
  var val = this[offset + --i];
  while (i > 0 && (mul *= 256)) {
    val += this[offset + --i] * mul;
  }
  mul *= 128;
  if (val >= mul)
    val -= Math.pow(2, 8 * byteLength2);
  return val;
};
Buffer.prototype.readInt8 = function readInt8(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 1, this.length);
  if (!(this[offset] & 128))
    return this[offset];
  return (255 - this[offset] + 1) * -1;
};
Buffer.prototype.readInt16LE = function readInt16LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  var val = this[offset] | this[offset + 1] << 8;
  return val & 32768 ? val | 4294901760 : val;
};
Buffer.prototype.readInt16BE = function readInt16BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  var val = this[offset + 1] | this[offset] << 8;
  return val & 32768 ? val | 4294901760 : val;
};
Buffer.prototype.readInt32LE = function readInt32LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] | this[offset + 1] << 8 | this[offset + 2] << 16 | this[offset + 3] << 24;
};
Buffer.prototype.readInt32BE = function readInt32BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] << 24 | this[offset + 1] << 16 | this[offset + 2] << 8 | this[offset + 3];
};
Buffer.prototype.readFloatLE = function readFloatLE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return read(this, offset, true, 23, 4);
};
Buffer.prototype.readFloatBE = function readFloatBE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return read(this, offset, false, 23, 4);
};
Buffer.prototype.readDoubleLE = function readDoubleLE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 8, this.length);
  return read(this, offset, true, 52, 8);
};
Buffer.prototype.readDoubleBE = function readDoubleBE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 8, this.length);
  return read(this, offset, false, 52, 8);
};
function checkInt(buf, value, offset, ext, max, min) {
  if (!internalIsBuffer(buf))
    throw new TypeError('"buffer" argument must be a Buffer instance');
  if (value > max || value < min)
    throw new RangeError('"value" argument is out of bounds');
  if (offset + ext > buf.length)
    throw new RangeError("Index out of range");
}
Buffer.prototype.writeUIntLE = function writeUIntLE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength2) - 1;
    checkInt(this, value, offset, byteLength2, maxBytes, 0);
  }
  var mul = 1;
  var i = 0;
  this[offset] = value & 255;
  while (++i < byteLength2 && (mul *= 256)) {
    this[offset + i] = value / mul & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeUIntBE = function writeUIntBE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength2) - 1;
    checkInt(this, value, offset, byteLength2, maxBytes, 0);
  }
  var i = byteLength2 - 1;
  var mul = 1;
  this[offset + i] = value & 255;
  while (--i >= 0 && (mul *= 256)) {
    this[offset + i] = value / mul & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeUInt8 = function writeUInt8(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 1, 255, 0);
  if (!Buffer.TYPED_ARRAY_SUPPORT)
    value = Math.floor(value);
  this[offset] = value & 255;
  return offset + 1;
};
function objectWriteUInt16(buf, value, offset, littleEndian) {
  if (value < 0)
    value = 65535 + value + 1;
  for (var i = 0, j = Math.min(buf.length - offset, 2); i < j; ++i) {
    buf[offset + i] = (value & 255 << 8 * (littleEndian ? i : 1 - i)) >>> (littleEndian ? i : 1 - i) * 8;
  }
}
Buffer.prototype.writeUInt16LE = function writeUInt16LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 65535, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
  } else {
    objectWriteUInt16(this, value, offset, true);
  }
  return offset + 2;
};
Buffer.prototype.writeUInt16BE = function writeUInt16BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 65535, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 8;
    this[offset + 1] = value & 255;
  } else {
    objectWriteUInt16(this, value, offset, false);
  }
  return offset + 2;
};
function objectWriteUInt32(buf, value, offset, littleEndian) {
  if (value < 0)
    value = 4294967295 + value + 1;
  for (var i = 0, j = Math.min(buf.length - offset, 4); i < j; ++i) {
    buf[offset + i] = value >>> (littleEndian ? i : 3 - i) * 8 & 255;
  }
}
Buffer.prototype.writeUInt32LE = function writeUInt32LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 4294967295, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset + 3] = value >>> 24;
    this[offset + 2] = value >>> 16;
    this[offset + 1] = value >>> 8;
    this[offset] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, true);
  }
  return offset + 4;
};
Buffer.prototype.writeUInt32BE = function writeUInt32BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 4294967295, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 24;
    this[offset + 1] = value >>> 16;
    this[offset + 2] = value >>> 8;
    this[offset + 3] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, false);
  }
  return offset + 4;
};
Buffer.prototype.writeIntLE = function writeIntLE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert) {
    var limit = Math.pow(2, 8 * byteLength2 - 1);
    checkInt(this, value, offset, byteLength2, limit - 1, -limit);
  }
  var i = 0;
  var mul = 1;
  var sub = 0;
  this[offset] = value & 255;
  while (++i < byteLength2 && (mul *= 256)) {
    if (value < 0 && sub === 0 && this[offset + i - 1] !== 0) {
      sub = 1;
    }
    this[offset + i] = (value / mul >> 0) - sub & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeIntBE = function writeIntBE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert) {
    var limit = Math.pow(2, 8 * byteLength2 - 1);
    checkInt(this, value, offset, byteLength2, limit - 1, -limit);
  }
  var i = byteLength2 - 1;
  var mul = 1;
  var sub = 0;
  this[offset + i] = value & 255;
  while (--i >= 0 && (mul *= 256)) {
    if (value < 0 && sub === 0 && this[offset + i + 1] !== 0) {
      sub = 1;
    }
    this[offset + i] = (value / mul >> 0) - sub & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeInt8 = function writeInt8(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 1, 127, -128);
  if (!Buffer.TYPED_ARRAY_SUPPORT)
    value = Math.floor(value);
  if (value < 0)
    value = 255 + value + 1;
  this[offset] = value & 255;
  return offset + 1;
};
Buffer.prototype.writeInt16LE = function writeInt16LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 32767, -32768);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
  } else {
    objectWriteUInt16(this, value, offset, true);
  }
  return offset + 2;
};
Buffer.prototype.writeInt16BE = function writeInt16BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 32767, -32768);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 8;
    this[offset + 1] = value & 255;
  } else {
    objectWriteUInt16(this, value, offset, false);
  }
  return offset + 2;
};
Buffer.prototype.writeInt32LE = function writeInt32LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 2147483647, -2147483648);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
    this[offset + 2] = value >>> 16;
    this[offset + 3] = value >>> 24;
  } else {
    objectWriteUInt32(this, value, offset, true);
  }
  return offset + 4;
};
Buffer.prototype.writeInt32BE = function writeInt32BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 2147483647, -2147483648);
  if (value < 0)
    value = 4294967295 + value + 1;
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 24;
    this[offset + 1] = value >>> 16;
    this[offset + 2] = value >>> 8;
    this[offset + 3] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, false);
  }
  return offset + 4;
};
function checkIEEE754(buf, value, offset, ext, max, min) {
  if (offset + ext > buf.length)
    throw new RangeError("Index out of range");
  if (offset < 0)
    throw new RangeError("Index out of range");
}
function writeFloat(buf, value, offset, littleEndian, noAssert) {
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 4);
  }
  write(buf, value, offset, littleEndian, 23, 4);
  return offset + 4;
}
Buffer.prototype.writeFloatLE = function writeFloatLE(value, offset, noAssert) {
  return writeFloat(this, value, offset, true, noAssert);
};
Buffer.prototype.writeFloatBE = function writeFloatBE(value, offset, noAssert) {
  return writeFloat(this, value, offset, false, noAssert);
};
function writeDouble(buf, value, offset, littleEndian, noAssert) {
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 8);
  }
  write(buf, value, offset, littleEndian, 52, 8);
  return offset + 8;
}
Buffer.prototype.writeDoubleLE = function writeDoubleLE(value, offset, noAssert) {
  return writeDouble(this, value, offset, true, noAssert);
};
Buffer.prototype.writeDoubleBE = function writeDoubleBE(value, offset, noAssert) {
  return writeDouble(this, value, offset, false, noAssert);
};
Buffer.prototype.copy = function copy(target, targetStart, start, end) {
  if (!start)
    start = 0;
  if (!end && end !== 0)
    end = this.length;
  if (targetStart >= target.length)
    targetStart = target.length;
  if (!targetStart)
    targetStart = 0;
  if (end > 0 && end < start)
    end = start;
  if (end === start)
    return 0;
  if (target.length === 0 || this.length === 0)
    return 0;
  if (targetStart < 0) {
    throw new RangeError("targetStart out of bounds");
  }
  if (start < 0 || start >= this.length)
    throw new RangeError("sourceStart out of bounds");
  if (end < 0)
    throw new RangeError("sourceEnd out of bounds");
  if (end > this.length)
    end = this.length;
  if (target.length - targetStart < end - start) {
    end = target.length - targetStart + start;
  }
  var len = end - start;
  var i;
  if (this === target && start < targetStart && targetStart < end) {
    for (i = len - 1; i >= 0; --i) {
      target[i + targetStart] = this[i + start];
    }
  } else if (len < 1e3 || !Buffer.TYPED_ARRAY_SUPPORT) {
    for (i = 0; i < len; ++i) {
      target[i + targetStart] = this[i + start];
    }
  } else {
    Uint8Array.prototype.set.call(target, this.subarray(start, start + len), targetStart);
  }
  return len;
};
Buffer.prototype.fill = function fill(val, start, end, encoding) {
  if (typeof val === "string") {
    if (typeof start === "string") {
      encoding = start;
      start = 0;
      end = this.length;
    } else if (typeof end === "string") {
      encoding = end;
      end = this.length;
    }
    if (val.length === 1) {
      var code = val.charCodeAt(0);
      if (code < 256) {
        val = code;
      }
    }
    if (encoding !== void 0 && typeof encoding !== "string") {
      throw new TypeError("encoding must be a string");
    }
    if (typeof encoding === "string" && !Buffer.isEncoding(encoding)) {
      throw new TypeError("Unknown encoding: " + encoding);
    }
  } else if (typeof val === "number") {
    val = val & 255;
  }
  if (start < 0 || this.length < start || this.length < end) {
    throw new RangeError("Out of range index");
  }
  if (end <= start) {
    return this;
  }
  start = start >>> 0;
  end = end === void 0 ? this.length : end >>> 0;
  if (!val)
    val = 0;
  var i;
  if (typeof val === "number") {
    for (i = start; i < end; ++i) {
      this[i] = val;
    }
  } else {
    var bytes = internalIsBuffer(val) ? val : utf8ToBytes(new Buffer(val, encoding).toString());
    var len = bytes.length;
    for (i = 0; i < end - start; ++i) {
      this[i + start] = bytes[i % len];
    }
  }
  return this;
};
var INVALID_BASE64_RE = /[^+\/0-9A-Za-z-_]/g;
function base64clean(str) {
  str = stringtrim(str).replace(INVALID_BASE64_RE, "");
  if (str.length < 2)
    return "";
  while (str.length % 4 !== 0) {
    str = str + "=";
  }
  return str;
}
function stringtrim(str) {
  if (str.trim)
    return str.trim();
  return str.replace(/^\s+|\s+$/g, "");
}
function toHex(n) {
  if (n < 16)
    return "0" + n.toString(16);
  return n.toString(16);
}
function utf8ToBytes(string, units) {
  units = units || Infinity;
  var codePoint;
  var length = string.length;
  var leadSurrogate = null;
  var bytes = [];
  for (var i = 0; i < length; ++i) {
    codePoint = string.charCodeAt(i);
    if (codePoint > 55295 && codePoint < 57344) {
      if (!leadSurrogate) {
        if (codePoint > 56319) {
          if ((units -= 3) > -1)
            bytes.push(239, 191, 189);
          continue;
        } else if (i + 1 === length) {
          if ((units -= 3) > -1)
            bytes.push(239, 191, 189);
          continue;
        }
        leadSurrogate = codePoint;
        continue;
      }
      if (codePoint < 56320) {
        if ((units -= 3) > -1)
          bytes.push(239, 191, 189);
        leadSurrogate = codePoint;
        continue;
      }
      codePoint = (leadSurrogate - 55296 << 10 | codePoint - 56320) + 65536;
    } else if (leadSurrogate) {
      if ((units -= 3) > -1)
        bytes.push(239, 191, 189);
    }
    leadSurrogate = null;
    if (codePoint < 128) {
      if ((units -= 1) < 0)
        break;
      bytes.push(codePoint);
    } else if (codePoint < 2048) {
      if ((units -= 2) < 0)
        break;
      bytes.push(codePoint >> 6 | 192, codePoint & 63 | 128);
    } else if (codePoint < 65536) {
      if ((units -= 3) < 0)
        break;
      bytes.push(codePoint >> 12 | 224, codePoint >> 6 & 63 | 128, codePoint & 63 | 128);
    } else if (codePoint < 1114112) {
      if ((units -= 4) < 0)
        break;
      bytes.push(codePoint >> 18 | 240, codePoint >> 12 & 63 | 128, codePoint >> 6 & 63 | 128, codePoint & 63 | 128);
    } else {
      throw new Error("Invalid code point");
    }
  }
  return bytes;
}
function asciiToBytes(str) {
  var byteArray = [];
  for (var i = 0; i < str.length; ++i) {
    byteArray.push(str.charCodeAt(i) & 255);
  }
  return byteArray;
}
function utf16leToBytes(str, units) {
  var c, hi, lo;
  var byteArray = [];
  for (var i = 0; i < str.length; ++i) {
    if ((units -= 2) < 0)
      break;
    c = str.charCodeAt(i);
    hi = c >> 8;
    lo = c % 256;
    byteArray.push(lo);
    byteArray.push(hi);
  }
  return byteArray;
}
function base64ToBytes(str) {
  return toByteArray(base64clean(str));
}
function blitBuffer(src, dst, offset, length) {
  for (var i = 0; i < length; ++i) {
    if (i + offset >= dst.length || i >= src.length)
      break;
    dst[i + offset] = src[i];
  }
  return i;
}
function isnan(val) {
  return val !== val;
}
function isBuffer$1(obj) {
  return obj != null && (!!obj._isBuffer || isFastBuffer(obj) || isSlowBuffer(obj));
}
function isFastBuffer(obj) {
  return !!obj.constructor && typeof obj.constructor.isBuffer === "function" && obj.constructor.isBuffer(obj);
}
function isSlowBuffer(obj) {
  return typeof obj.readFloatLE === "function" && typeof obj.slice === "function" && isFastBuffer(obj.slice(0, 0));
}
function isVisitable(thing) {
  return utils.isPlainObject(thing) || utils.isArray(thing);
}
function removeBrackets(key) {
  return utils.endsWith(key, "[]") ? key.slice(0, -2) : key;
}
function renderKey(path, key, dots) {
  if (!path)
    return key;
  return path.concat(key).map(function each(token, i) {
    token = removeBrackets(token);
    return !dots && i ? "[" + token + "]" : token;
  }).join(dots ? "." : "");
}
function isFlatArray(arr) {
  return utils.isArray(arr) && !arr.some(isVisitable);
}
const predicates = utils.toFlatObject(utils, {}, null, function filter(prop) {
  return /^is[A-Z]/.test(prop);
});
function toFormData(obj, formData, options) {
  if (!utils.isObject(obj)) {
    throw new TypeError("target must be an object");
  }
  formData = formData || new FormData();
  options = utils.toFlatObject(options, {
    metaTokens: true,
    dots: false,
    indexes: false
  }, false, function defined(option, source) {
    return !utils.isUndefined(source[option]);
  });
  const metaTokens = options.metaTokens;
  const visitor = options.visitor || defaultVisitor;
  const dots = options.dots;
  const indexes = options.indexes;
  const _Blob = options.Blob || typeof Blob !== "undefined" && Blob;
  const useBlob = _Blob && utils.isSpecCompliantForm(formData);
  if (!utils.isFunction(visitor)) {
    throw new TypeError("visitor must be a function");
  }
  function convertValue(value) {
    if (value === null)
      return "";
    if (utils.isDate(value)) {
      return value.toISOString();
    }
    if (!useBlob && utils.isBlob(value)) {
      throw new AxiosError("Blob is not supported. Use a Buffer instead.");
    }
    if (utils.isArrayBuffer(value) || utils.isTypedArray(value)) {
      return useBlob && typeof Blob === "function" ? new Blob([value]) : Buffer.from(value);
    }
    return value;
  }
  function defaultVisitor(value, key, path) {
    let arr = value;
    if (value && !path && typeof value === "object") {
      if (utils.endsWith(key, "{}")) {
        key = metaTokens ? key : key.slice(0, -2);
        value = JSON.stringify(value);
      } else if (utils.isArray(value) && isFlatArray(value) || (utils.isFileList(value) || utils.endsWith(key, "[]")) && (arr = utils.toArray(value))) {
        key = removeBrackets(key);
        arr.forEach(function each(el, index) {
          !(utils.isUndefined(el) || el === null) && formData.append(indexes === true ? renderKey([key], index, dots) : indexes === null ? key : key + "[]", convertValue(el));
        });
        return false;
      }
    }
    if (isVisitable(value)) {
      return true;
    }
    formData.append(renderKey(path, key, dots), convertValue(value));
    return false;
  }
  const stack = [];
  const exposedHelpers = Object.assign(predicates, {
    defaultVisitor,
    convertValue,
    isVisitable
  });
  function build(value, path) {
    if (utils.isUndefined(value))
      return;
    if (stack.indexOf(value) !== -1) {
      throw Error("Circular reference detected in " + path.join("."));
    }
    stack.push(value);
    utils.forEach(value, function each(el, key) {
      const result = !(utils.isUndefined(el) || el === null) && visitor.call(formData, el, utils.isString(key) ? key.trim() : key, path, exposedHelpers);
      if (result === true) {
        build(el, path ? path.concat(key) : [key]);
      }
    });
    stack.pop();
  }
  if (!utils.isObject(obj)) {
    throw new TypeError("data must be an object");
  }
  build(obj);
  return formData;
}
function encode(str) {
  const charMap = {
    "!": "%21",
    "'": "%27",
    "(": "%28",
    ")": "%29",
    "~": "%7E",
    "%20": "+",
    "%00": "\0"
  };
  return encodeURIComponent(str).replace(/[!'()~]|%20|%00/g, function replacer(match) {
    return charMap[match];
  });
}
function AxiosURLSearchParams(params, options) {
  this._pairs = [];
  params && toFormData(params, this, options);
}
const prototype$1 = AxiosURLSearchParams.prototype;
prototype$1.append = function append(name, value) {
  this._pairs.push([name, value]);
};
prototype$1.toString = function toString3(encoder) {
  const _encode = encoder ? function(value) {
    return encoder.call(this, value, encode);
  } : encode;
  return this._pairs.map(function each(pair) {
    return _encode(pair[0]) + "=" + _encode(pair[1]);
  }, "").join("&");
};
function encode$1(val) {
  return encodeURIComponent(val).replace(/%3A/gi, ":").replace(/%24/g, "$").replace(/%2C/gi, ",").replace(/%20/g, "+").replace(/%5B/gi, "[").replace(/%5D/gi, "]");
}
function buildURL(url, params, options) {
  if (!params) {
    return url;
  }
  const _encode = options && options.encode || encode$1;
  const serializeFn = options && options.serialize;
  let serializedParams;
  if (serializeFn) {
    serializedParams = serializeFn(params, options);
  } else {
    serializedParams = utils.isURLSearchParams(params) ? params.toString() : new AxiosURLSearchParams(params, options).toString(_encode);
  }
  if (serializedParams) {
    const hashmarkIndex = url.indexOf("#");
    if (hashmarkIndex !== -1) {
      url = url.slice(0, hashmarkIndex);
    }
    url += (url.indexOf("?") === -1 ? "?" : "&") + serializedParams;
  }
  return url;
}

function settle(resolve, reject, response) {
  const validateStatus = response.config.validateStatus;
  if (!response.status || !validateStatus || validateStatus(response.status)) {
    resolve(response);
  } else {
    reject(new AxiosError("Request failed with status code " + response.status, [AxiosError.ERR_BAD_REQUEST, AxiosError.ERR_BAD_RESPONSE][Math.floor(response.status / 100) - 4], response.config, response.request, response));
  }
}

function isAbsoluteURL(url) {
  return /^([a-z][a-z\d+\-.]*:)?\/\//i.test(url);
}

function combineURLs(baseURL, relativeURL) {
  return relativeURL ? baseURL.replace(/\/+$/, "") + "/" + relativeURL.replace(/^\/+/, "") : baseURL;
}

function buildFullPath(baseURL, requestedURL) {
  if (baseURL && !isAbsoluteURL(requestedURL)) {
    return combineURLs(baseURL, requestedURL);
  }
  return requestedURL;
}

var transitionalDefaults = {
  silentJSONParsing: true,
  forcedJSONParsing: true,
  clarifyTimeoutError: false
};
var URLSearchParams$1 = typeof URLSearchParams !== "undefined" ? URLSearchParams : AxiosURLSearchParams;
var FormData$1 = typeof FormData !== "undefined" ? FormData : null;
var Blob$1 = typeof Blob !== "undefined" ? Blob : null;
const isStandardBrowserEnv = (() => {
  let product;
  if (typeof navigator !== "undefined" && ((product = navigator.product) === "ReactNative" || product === "NativeScript" || product === "NS")) {
    return false;
  }
  return typeof window !== "undefined" && typeof document !== "undefined";
})();
const isStandardBrowserWebWorkerEnv = (() => {
  return typeof WorkerGlobalScope !== "undefined" && self instanceof WorkerGlobalScope && typeof self.importScripts === "function";
})();
var platform = {
  isBrowser: true,
  classes: {
    URLSearchParams: URLSearchParams$1,
    FormData: FormData$1,
    Blob: Blob$1
  },
  isStandardBrowserEnv,
  isStandardBrowserWebWorkerEnv,
  protocols: ["http", "https", "file", "blob", "url", "data"]
};
const ignoreDuplicateOf = utils.toObjectSet([
  "age",
  "authorization",
  "content-length",
  "content-type",
  "etag",
  "expires",
  "from",
  "host",
  "if-modified-since",
  "if-unmodified-since",
  "last-modified",
  "location",
  "max-forwards",
  "proxy-authorization",
  "referer",
  "retry-after",
  "user-agent"
]);
var parseHeaders = (rawHeaders) => {
  const parsed = {};
  let key;
  let val;
  let i;
  rawHeaders && rawHeaders.split("\n").forEach(function parser(line) {
    i = line.indexOf(":");
    key = line.substring(0, i).trim().toLowerCase();
    val = line.substring(i + 1).trim();
    if (!key || parsed[key] && ignoreDuplicateOf[key]) {
      return;
    }
    if (key === "set-cookie") {
      if (parsed[key]) {
        parsed[key].push(val);
      } else {
        parsed[key] = [val];
      }
    } else {
      parsed[key] = parsed[key] ? parsed[key] + ", " + val : val;
    }
  });
  return parsed;
};
const $internals = Symbol("internals");
function normalizeHeader(header) {
  return header && String(header).trim().toLowerCase();
}
function normalizeValue(value) {
  if (value === false || value == null) {
    return value;
  }
  return utils.isArray(value) ? value.map(normalizeValue) : String(value);
}
function parseTokens(str) {
  const tokens = Object.create(null);
  const tokensRE = /([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;
  let match;
  while (match = tokensRE.exec(str)) {
    tokens[match[1]] = match[2];
  }
  return tokens;
}
const isValidHeaderName = (str) => /^[-_a-zA-Z0-9^`|~,!#$%&'*+.]+$/.test(str.trim());
function matchHeaderValue(context, value, header, filter, isHeaderNameFilter) {
  if (utils.isFunction(filter)) {
    return filter.call(this, value, header);
  }
  if (isHeaderNameFilter) {
    value = header;
  }
  if (!utils.isString(value))
    return;
  if (utils.isString(filter)) {
    return value.indexOf(filter) !== -1;
  }
  if (utils.isRegExp(filter)) {
    return filter.test(value);
  }
}
function formatHeader(header) {
  return header.trim().toLowerCase().replace(/([a-z\d])(\w*)/g, (w, char, str) => {
    return char.toUpperCase() + str;
  });
}
function buildAccessors(obj, header) {
  const accessorName = utils.toCamelCase(" " + header);
  ["get", "set", "has"].forEach((methodName) => {
    Object.defineProperty(obj, methodName + accessorName, {
      value: function(arg1, arg2, arg3) {
        return this[methodName].call(this, header, arg1, arg2, arg3);
      },
      configurable: true
    });
  });
}
class AxiosHeaders {
  constructor(headers) {
    headers && this.set(headers);
  }
  set(header, valueOrRewrite, rewrite) {
    const self2 = this;
    function setHeader(_value, _header, _rewrite) {
      const lHeader = normalizeHeader(_header);
      if (!lHeader) {
        throw new Error("header name must be a non-empty string");
      }
      const key = utils.findKey(self2, lHeader);
      if (!key || self2[key] === void 0 || _rewrite === true || _rewrite === void 0 && self2[key] !== false) {
        self2[key || _header] = normalizeValue(_value);
      }
    }
    const setHeaders = (headers, _rewrite) => utils.forEach(headers, (_value, _header) => setHeader(_value, _header, _rewrite));
    if (utils.isPlainObject(header) || header instanceof this.constructor) {
      setHeaders(header, valueOrRewrite);
    } else if (utils.isString(header) && (header = header.trim()) && !isValidHeaderName(header)) {
      setHeaders(parseHeaders(header), valueOrRewrite);
    } else {
      header != null && setHeader(valueOrRewrite, header, rewrite);
    }
    return this;
  }
  get(header, parser) {
    header = normalizeHeader(header);
    if (header) {
      const key = utils.findKey(this, header);
      if (key) {
        const value = this[key];
        if (!parser) {
          return value;
        }
        if (parser === true) {
          return parseTokens(value);
        }
        if (utils.isFunction(parser)) {
          return parser.call(this, value, key);
        }
        if (utils.isRegExp(parser)) {
          return parser.exec(value);
        }
        throw new TypeError("parser must be boolean|regexp|function");
      }
    }
  }
  has(header, matcher) {
    header = normalizeHeader(header);
    if (header) {
      const key = utils.findKey(this, header);
      return !!(key && this[key] !== void 0 && (!matcher || matchHeaderValue(this, this[key], key, matcher)));
    }
    return false;
  }
  delete(header, matcher) {
    const self2 = this;
    let deleted = false;
    function deleteHeader(_header) {
      _header = normalizeHeader(_header);
      if (_header) {
        const key = utils.findKey(self2, _header);
        if (key && (!matcher || matchHeaderValue(self2, self2[key], key, matcher))) {
          delete self2[key];
          deleted = true;
        }
      }
    }
    if (utils.isArray(header)) {
      header.forEach(deleteHeader);
    } else {
      deleteHeader(header);
    }
    return deleted;
  }
  clear(matcher) {
    const keys = Object.keys(this);
    let i = keys.length;
    let deleted = false;
    while (i--) {
      const key = keys[i];
      if (!matcher || matchHeaderValue(this, this[key], key, matcher, true)) {
        delete this[key];
        deleted = true;
      }
    }
    return deleted;
  }
  normalize(format) {
    const self2 = this;
    const headers = {};
    utils.forEach(this, (value, header) => {
      const key = utils.findKey(headers, header);
      if (key) {
        self2[key] = normalizeValue(value);
        delete self2[header];
        return;
      }
      const normalized = format ? formatHeader(header) : String(header).trim();
      if (normalized !== header) {
        delete self2[header];
      }
      self2[normalized] = normalizeValue(value);
      headers[normalized] = true;
    });
    return this;
  }
  concat(...targets) {
    return this.constructor.concat(this, ...targets);
  }
  toJSON(asStrings) {
    const obj = Object.create(null);
    utils.forEach(this, (value, header) => {
      value != null && value !== false && (obj[header] = asStrings && utils.isArray(value) ? value.join(", ") : value);
    });
    return obj;
  }
  [Symbol.iterator]() {
    return Object.entries(this.toJSON())[Symbol.iterator]();
  }
  toString() {
    return Object.entries(this.toJSON()).map(([header, value]) => header + ": " + value).join("\n");
  }
  get [Symbol.toStringTag]() {
    return "AxiosHeaders";
  }
  static from(thing) {
    return thing instanceof this ? thing : new this(thing);
  }
  static concat(first, ...targets) {
    const computed = new this(first);
    targets.forEach((target) => computed.set(target));
    return computed;
  }
  static accessor(header) {
    const internals = this[$internals] = this[$internals] = {
      accessors: {}
    };
    const accessors = internals.accessors;
    const prototype = this.prototype;
    function defineAccessor(_header) {
      const lHeader = normalizeHeader(_header);
      if (!accessors[lHeader]) {
        buildAccessors(prototype, _header);
        accessors[lHeader] = true;
      }
    }
    utils.isArray(header) ? header.forEach(defineAccessor) : defineAccessor(header);
    return this;
  }
}
AxiosHeaders.accessor(["Content-Type", "Content-Length", "Accept", "Accept-Encoding", "User-Agent", "Authorization"]);
utils.freezeMethods(AxiosHeaders.prototype);
utils.freezeMethods(AxiosHeaders);
function CanceledError(message, config, request) {
  AxiosError.call(this, message == null ? "canceled" : message, AxiosError.ERR_CANCELED, config, request);
  this.name = "CanceledError";
}
utils.inherits(CanceledError, AxiosError, {
  __CANCEL__: true
});
var cookies = platform.isStandardBrowserEnv ? function standardBrowserEnv() {
  return {
    write: function write(name, value, expires, path, domain, secure) {
      const cookie = [];
      cookie.push(name + "=" + encodeURIComponent(value));
      if (utils.isNumber(expires)) {
        cookie.push("expires=" + new Date(expires).toGMTString());
      }
      if (utils.isString(path)) {
        cookie.push("path=" + path);
      }
      if (utils.isString(domain)) {
        cookie.push("domain=" + domain);
      }
      if (secure === true) {
        cookie.push("secure");
      }
      document.cookie = cookie.join("; ");
    },
    read: function read(name) {
      const match = document.cookie.match(new RegExp("(^|;\\s*)(" + name + ")=([^;]*)"));
      return match ? decodeURIComponent(match[3]) : null;
    },
    remove: function remove(name) {
      this.write(name, "", Date.now() - 864e5);
    }
  };
}() : function nonStandardBrowserEnv() {
  return {
    write: function write() {
    },
    read: function read() {
      return null;
    },
    remove: function remove() {
    }
  };
}();
var isURLSameOrigin = platform.isStandardBrowserEnv ? function standardBrowserEnv2() {
  const msie = /(msie|trident)/i.test(navigator.userAgent);
  const urlParsingNode = document.createElement("a");
  let originURL;
  function resolveURL(url) {
    let href = url;
    if (msie) {
      urlParsingNode.setAttribute("href", href);
      href = urlParsingNode.href;
    }
    urlParsingNode.setAttribute("href", href);
    return {
      href: urlParsingNode.href,
      protocol: urlParsingNode.protocol ? urlParsingNode.protocol.replace(/:$/, "") : "",
      host: urlParsingNode.host,
      search: urlParsingNode.search ? urlParsingNode.search.replace(/^\?/, "") : "",
      hash: urlParsingNode.hash ? urlParsingNode.hash.replace(/^#/, "") : "",
      hostname: urlParsingNode.hostname,
      port: urlParsingNode.port,
      pathname: urlParsingNode.pathname.charAt(0) === "/" ? urlParsingNode.pathname : "/" + urlParsingNode.pathname
    };
  }
  originURL = resolveURL(window.location.href);
  return function isURLSameOrigin2(requestURL) {
    const parsed = utils.isString(requestURL) ? resolveURL(requestURL) : requestURL;
    return parsed.protocol === originURL.protocol && parsed.host === originURL.host;
  };
}() : function nonStandardBrowserEnv2() {
  return function isURLSameOrigin2() {
    return true;
  };
}();
function parseProtocol(url) {
  const match = /^([-+\w]{1,25})(:?\/\/|:)/.exec(url);
  return match && match[1] || "";
}
function speedometer(samplesCount, min) {
  samplesCount = samplesCount || 10;
  const bytes = new Array(samplesCount);
  const timestamps = new Array(samplesCount);
  let head = 0;
  let tail = 0;
  let firstSampleTS;
  min = min !== void 0 ? min : 1e3;
  return function push(chunkLength) {
    const now = Date.now();
    const startedAt = timestamps[tail];
    if (!firstSampleTS) {
      firstSampleTS = now;
    }
    bytes[head] = chunkLength;
    timestamps[head] = now;
    let i = tail;
    let bytesCount = 0;
    while (i !== head) {
      bytesCount += bytes[i++];
      i = i % samplesCount;
    }
    head = (head + 1) % samplesCount;
    if (head === tail) {
      tail = (tail + 1) % samplesCount;
    }
    if (now - firstSampleTS < min) {
      return;
    }
    const passed = startedAt && now - startedAt;
    return passed ? Math.round(bytesCount * 1e3 / passed) : void 0;
  };
}
function progressEventReducer(listener, isDownloadStream) {
  let bytesNotified = 0;
  const _speedometer = speedometer(50, 250);
  return (e) => {
    const loaded = e.loaded;
    const total = e.lengthComputable ? e.total : void 0;
    const progressBytes = loaded - bytesNotified;
    const rate = _speedometer(progressBytes);
    const inRange = loaded <= total;
    bytesNotified = loaded;
    const data = {
      loaded,
      total,
      progress: total ? loaded / total : void 0,
      bytes: progressBytes,
      rate: rate ? rate : void 0,
      estimated: rate && total && inRange ? (total - loaded) / rate : void 0,
      event: e
    };
    data[isDownloadStream ? "download" : "upload"] = true;
    listener(data);
  };
}
const isXHRAdapterSupported = typeof XMLHttpRequest !== "undefined";
var xhrAdapter = isXHRAdapterSupported && function(config) {
  return new Promise(function dispatchXhrRequest(resolve, reject) {
    let requestData = config.data;
    const requestHeaders = AxiosHeaders.from(config.headers).normalize();
    const responseType = config.responseType;
    let onCanceled;
    function done() {
      if (config.cancelToken) {
        config.cancelToken.unsubscribe(onCanceled);
      }
      if (config.signal) {
        config.signal.removeEventListener("abort", onCanceled);
      }
    }
    if (utils.isFormData(requestData)) {
      if (platform.isStandardBrowserEnv || platform.isStandardBrowserWebWorkerEnv) {
        requestHeaders.setContentType(false);
      } else {
        requestHeaders.setContentType("multipart/form-data;", false);
      }
    }
    let request = new XMLHttpRequest();
    if (config.auth) {
      const username = config.auth.username || "";
      const password = config.auth.password ? unescape(encodeURIComponent(config.auth.password)) : "";
      requestHeaders.set("Authorization", "Basic " + btoa(username + ":" + password));
    }
    const fullPath = buildFullPath(config.baseURL, config.url);
    request.open(config.method.toUpperCase(), buildURL(fullPath, config.params, config.paramsSerializer), true);
    request.timeout = config.timeout;
    function onloadend() {
      if (!request) {
        return;
      }
      const responseHeaders = AxiosHeaders.from("getAllResponseHeaders" in request && request.getAllResponseHeaders());
      const responseData = !responseType || responseType === "text" || responseType === "json" ? request.responseText : request.response;
      const response = {
        data: responseData,
        status: request.status,
        statusText: request.statusText,
        headers: responseHeaders,
        config,
        request
      };
      settle(function _resolve(value) {
        resolve(value);
        done();
      }, function _reject(err) {
        reject(err);
        done();
      }, response);
      request = null;
    }
    if ("onloadend" in request) {
      request.onloadend = onloadend;
    } else {
      request.onreadystatechange = function handleLoad() {
        if (!request || request.readyState !== 4) {
          return;
        }
        if (request.status === 0 && !(request.responseURL && request.responseURL.indexOf("file:") === 0)) {
          return;
        }
        setTimeout(onloadend);
      };
    }
    request.onabort = function handleAbort() {
      if (!request) {
        return;
      }
      reject(new AxiosError("Request aborted", AxiosError.ECONNABORTED, config, request));
      request = null;
    };
    request.onerror = function handleError() {
      reject(new AxiosError("Network Error", AxiosError.ERR_NETWORK, config, request));
      request = null;
    };
    request.ontimeout = function handleTimeout() {
      let timeoutErrorMessage = config.timeout ? "timeout of " + config.timeout + "ms exceeded" : "timeout exceeded";
      const transitional = config.transitional || transitionalDefaults;
      if (config.timeoutErrorMessage) {
        timeoutErrorMessage = config.timeoutErrorMessage;
      }
      reject(new AxiosError(timeoutErrorMessage, transitional.clarifyTimeoutError ? AxiosError.ETIMEDOUT : AxiosError.ECONNABORTED, config, request));
      request = null;
    };
    if (platform.isStandardBrowserEnv) {
      const xsrfValue = (config.withCredentials || isURLSameOrigin(fullPath)) && config.xsrfCookieName && cookies.read(config.xsrfCookieName);
      if (xsrfValue) {
        requestHeaders.set(config.xsrfHeaderName, xsrfValue);
      }
    }
    requestData === void 0 && requestHeaders.setContentType(null);
    if ("setRequestHeader" in request) {
      utils.forEach(requestHeaders.toJSON(), function setRequestHeader(val, key) {
        request.setRequestHeader(key, val);
      });
    }
    if (!utils.isUndefined(config.withCredentials)) {
      request.withCredentials = !!config.withCredentials;
    }
    if (responseType && responseType !== "json") {
      request.responseType = config.responseType;
    }
    if (typeof config.onDownloadProgress === "function") {
      request.addEventListener("progress", progressEventReducer(config.onDownloadProgress, true));
    }
    if (typeof config.onUploadProgress === "function" && request.upload) {
      request.upload.addEventListener("progress", progressEventReducer(config.onUploadProgress));
    }
    if (config.cancelToken || config.signal) {
      onCanceled = (cancel) => {
        if (!request) {
          return;
        }
        reject(!cancel || cancel.type ? new CanceledError(null, config, request) : cancel);
        request.abort();
        request = null;
      };
      config.cancelToken && config.cancelToken.subscribe(onCanceled);
      if (config.signal) {
        config.signal.aborted ? onCanceled() : config.signal.addEventListener("abort", onCanceled);
      }
    }
    const protocol = parseProtocol(fullPath);
    if (protocol && platform.protocols.indexOf(protocol) === -1) {
      reject(new AxiosError("Unsupported protocol " + protocol + ":", AxiosError.ERR_BAD_REQUEST, config));
      return;
    }
    request.send(requestData || null);
  });
};

var httpAdapter = null;

class InterceptorManager {
  constructor() {
    this.handlers = [];
  }
  use(fulfilled, rejected, options) {
    this.handlers.push({
      fulfilled,
      rejected,
      synchronous: options ? options.synchronous : false,
      runWhen: options ? options.runWhen : null
    });
    return this.handlers.length - 1;
  }
  eject(id) {
    if (this.handlers[id]) {
      this.handlers[id] = null;
    }
  }
  clear() {
    if (this.handlers) {
      this.handlers = [];
    }
  }
  forEach(fn) {
    utils.forEach(this.handlers, function forEachHandler(h) {
      if (h !== null) {
        fn(h);
      }
    });
  }
}
function toURLEncodedForm(data, options) {
  return toFormData(data, new platform.classes.URLSearchParams(), Object.assign({
    visitor: function(value, key, path, helpers) {
      return helpers.defaultVisitor.apply(this, arguments);
    }
  }, options));
}
function parsePropPath(name) {
  return utils.matchAll(/\w+|\[(\w*)]/g, name).map((match) => {
    return match[0] === "[]" ? "" : match[1] || match[0];
  });
}
function arrayToObject(arr) {
  const obj = {};
  const keys = Object.keys(arr);
  let i;
  const len = keys.length;
  let key;
  for (i = 0; i < len; i++) {
    key = keys[i];
    obj[key] = arr[key];
  }
  return obj;
}
function formDataToJSON(formData) {
  function buildPath(path, value, target, index) {
    let name = path[index++];
    const isNumericKey = Number.isFinite(+name);
    const isLast = index >= path.length;
    name = !name && utils.isArray(target) ? target.length : name;
    if (isLast) {
      if (utils.hasOwnProp(target, name)) {
        target[name] = [target[name], value];
      } else {
        target[name] = value;
      }
      return !isNumericKey;
    }
    if (!target[name] || !utils.isObject(target[name])) {
      target[name] = [];
    }
    const result = buildPath(path, value, target[name], index);
    if (result && utils.isArray(target[name])) {
      target[name] = arrayToObject(target[name]);
    }
    return !isNumericKey;
  }
  if (utils.isFormData(formData) && utils.isFunction(formData.entries)) {
    const obj = {};
    utils.forEachEntry(formData, (name, value) => {
      buildPath(parsePropPath(name), value, obj, 0);
    });
    return obj;
  }
  return null;
}
const DEFAULT_CONTENT_TYPE = {
  "Content-Type": void 0
};
function stringifySafely(rawValue, parser, encoder) {
  if (utils.isString(rawValue)) {
    try {
      (parser || JSON.parse)(rawValue);
      return utils.trim(rawValue);
    } catch (e) {
      if (e.name !== "SyntaxError") {
        throw e;
      }
    }
  }
  return (encoder || JSON.stringify)(rawValue);
}
const defaults = {
  transitional: transitionalDefaults,
  adapter: ["xhr", "http"],
  transformRequest: [function transformRequest(data, headers) {
    const contentType = headers.getContentType() || "";
    const hasJSONContentType = contentType.indexOf("application/json") > -1;
    const isObjectPayload = utils.isObject(data);
    if (isObjectPayload && utils.isHTMLForm(data)) {
      data = new FormData(data);
    }
    const isFormData = utils.isFormData(data);
    if (isFormData) {
      if (!hasJSONContentType) {
        return data;
      }
      return hasJSONContentType ? JSON.stringify(formDataToJSON(data)) : data;
    }
    if (utils.isArrayBuffer(data) || utils.isBuffer(data) || utils.isStream(data) || utils.isFile(data) || utils.isBlob(data)) {
      return data;
    }
    if (utils.isArrayBufferView(data)) {
      return data.buffer;
    }
    if (utils.isURLSearchParams(data)) {
      headers.setContentType("application/x-www-form-urlencoded;charset=utf-8", false);
      return data.toString();
    }
    let isFileList;
    if (isObjectPayload) {
      if (contentType.indexOf("application/x-www-form-urlencoded") > -1) {
        return toURLEncodedForm(data, this.formSerializer).toString();
      }
      if ((isFileList = utils.isFileList(data)) || contentType.indexOf("multipart/form-data") > -1) {
        const _FormData = this.env && this.env.FormData;
        return toFormData(isFileList ? {"files[]": data} : data, _FormData && new _FormData(), this.formSerializer);
      }
    }
    if (isObjectPayload || hasJSONContentType) {
      headers.setContentType("application/json", false);
      return stringifySafely(data);
    }
    return data;
  }],
  transformResponse: [function transformResponse(data) {
    const transitional2 = this.transitional || defaults.transitional;
    const forcedJSONParsing = transitional2 && transitional2.forcedJSONParsing;
    const JSONRequested = this.responseType === "json";
    if (data && utils.isString(data) && (forcedJSONParsing && !this.responseType || JSONRequested)) {
      const silentJSONParsing = transitional2 && transitional2.silentJSONParsing;
      const strictJSONParsing = !silentJSONParsing && JSONRequested;
      try {
        return JSON.parse(data);
      } catch (e) {
        if (strictJSONParsing) {
          if (e.name === "SyntaxError") {
            throw AxiosError.from(e, AxiosError.ERR_BAD_RESPONSE, this, null, this.response);
          }
          throw e;
        }
      }
    }
    return data;
  }],
  timeout: 0,
  xsrfCookieName: "XSRF-TOKEN",
  xsrfHeaderName: "X-XSRF-TOKEN",
  maxContentLength: -1,
  maxBodyLength: -1,
  env: {
    FormData: platform.classes.FormData,
    Blob: platform.classes.Blob
  },
  validateStatus: function validateStatus(status) {
    return status >= 200 && status < 300;
  },
  headers: {
    common: {
      Accept: "application/json, text/plain, */*"
    }
  }
};
utils.forEach(["delete", "get", "head"], function forEachMethodNoData(method) {
  defaults.headers[method] = {};
});
utils.forEach(["post", "put", "patch"], function forEachMethodWithData(method) {
  defaults.headers[method] = utils.merge(DEFAULT_CONTENT_TYPE);
});
function transformData(fns, response) {
  const config = this || defaults;
  const context = response || config;
  const headers = AxiosHeaders.from(context.headers);
  let data = context.data;
  utils.forEach(fns, function transform(fn) {
    data = fn.call(config, data, headers.normalize(), response ? response.status : void 0);
  });
  headers.normalize();
  return data;
}
function isCancel(value) {
  return !!(value && value.__CANCEL__);
}
const knownAdapters = {
  http: httpAdapter,
  xhr: xhrAdapter
};
utils.forEach(knownAdapters, (fn, value) => {
  if (fn) {
    try {
      Object.defineProperty(fn, "name", {value});
    } catch (e) {
    }
    Object.defineProperty(fn, "adapterName", {value});
  }
});
var adapters = {
  getAdapter: (adapters2) => {
    adapters2 = utils.isArray(adapters2) ? adapters2 : [adapters2];
    const {length} = adapters2;
    let nameOrAdapter;
    let adapter;
    for (let i = 0; i < length; i++) {
      nameOrAdapter = adapters2[i];
      if (adapter = utils.isString(nameOrAdapter) ? knownAdapters[nameOrAdapter.toLowerCase()] : nameOrAdapter) {
        break;
      }
    }
    if (!adapter) {
      if (adapter === false) {
        throw new AxiosError(`Adapter ${nameOrAdapter} is not supported by the environment`, "ERR_NOT_SUPPORT");
      }
      throw new Error(utils.hasOwnProp(knownAdapters, nameOrAdapter) ? `Adapter '${nameOrAdapter}' is not available in the build` : `Unknown adapter '${nameOrAdapter}'`);
    }
    if (!utils.isFunction(adapter)) {
      throw new TypeError("adapter is not a function");
    }
    return adapter;
  },
  adapters: knownAdapters
};
function throwIfCancellationRequested(config) {
  if (config.cancelToken) {
    config.cancelToken.throwIfRequested();
  }
  if (config.signal && config.signal.aborted) {
    throw new CanceledError(null, config);
  }
}
function dispatchRequest(config) {
  throwIfCancellationRequested(config);
  config.headers = AxiosHeaders.from(config.headers);
  config.data = transformData.call(config, config.transformRequest);
  if (["post", "put", "patch"].indexOf(config.method) !== -1) {
    config.headers.setContentType("application/x-www-form-urlencoded", false);
  }
  const adapter = adapters.getAdapter(config.adapter || defaults.adapter);
  return adapter(config).then(function onAdapterResolution(response) {
    throwIfCancellationRequested(config);
    response.data = transformData.call(config, config.transformResponse, response);
    response.headers = AxiosHeaders.from(response.headers);
    return response;
  }, function onAdapterRejection(reason) {
    if (!isCancel(reason)) {
      throwIfCancellationRequested(config);
      if (reason && reason.response) {
        reason.response.data = transformData.call(config, config.transformResponse, reason.response);
        reason.response.headers = AxiosHeaders.from(reason.response.headers);
      }
    }
    return Promise.reject(reason);
  });
}
const headersToObject = (thing) => thing instanceof AxiosHeaders ? thing.toJSON() : thing;
function mergeConfig(config1, config2) {
  config2 = config2 || {};
  const config = {};
  function getMergedValue(target, source, caseless) {
    if (utils.isPlainObject(target) && utils.isPlainObject(source)) {
      return utils.merge.call({caseless}, target, source);
    } else if (utils.isPlainObject(source)) {
      return utils.merge({}, source);
    } else if (utils.isArray(source)) {
      return source.slice();
    }
    return source;
  }
  function mergeDeepProperties(a, b, caseless) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(a, b, caseless);
    } else if (!utils.isUndefined(a)) {
      return getMergedValue(void 0, a, caseless);
    }
  }
  function valueFromConfig2(a, b) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(void 0, b);
    }
  }
  function defaultToConfig2(a, b) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(void 0, b);
    } else if (!utils.isUndefined(a)) {
      return getMergedValue(void 0, a);
    }
  }
  function mergeDirectKeys(a, b, prop) {
    if (prop in config2) {
      return getMergedValue(a, b);
    } else if (prop in config1) {
      return getMergedValue(void 0, a);
    }
  }
  const mergeMap = {
    url: valueFromConfig2,
    method: valueFromConfig2,
    data: valueFromConfig2,
    baseURL: defaultToConfig2,
    transformRequest: defaultToConfig2,
    transformResponse: defaultToConfig2,
    paramsSerializer: defaultToConfig2,
    timeout: defaultToConfig2,
    timeoutMessage: defaultToConfig2,
    withCredentials: defaultToConfig2,
    adapter: defaultToConfig2,
    responseType: defaultToConfig2,
    xsrfCookieName: defaultToConfig2,
    xsrfHeaderName: defaultToConfig2,
    onUploadProgress: defaultToConfig2,
    onDownloadProgress: defaultToConfig2,
    decompress: defaultToConfig2,
    maxContentLength: defaultToConfig2,
    maxBodyLength: defaultToConfig2,
    beforeRedirect: defaultToConfig2,
    transport: defaultToConfig2,
    httpAgent: defaultToConfig2,
    httpsAgent: defaultToConfig2,
    cancelToken: defaultToConfig2,
    socketPath: defaultToConfig2,
    responseEncoding: defaultToConfig2,
    validateStatus: mergeDirectKeys,
    headers: (a, b) => mergeDeepProperties(headersToObject(a), headersToObject(b), true)
  };
  utils.forEach(Object.keys(Object.assign({}, config1, config2)), function computeConfigValue(prop) {
    const merge = mergeMap[prop] || mergeDeepProperties;
    const configValue = merge(config1[prop], config2[prop], prop);
    utils.isUndefined(configValue) && merge !== mergeDirectKeys || (config[prop] = configValue);
  });
  return config;
}
const VERSION = "1.4.0";
const validators = {};
["object", "boolean", "number", "function", "string", "symbol"].forEach((type, i) => {
  validators[type] = function validator2(thing) {
    return typeof thing === type || "a" + (i < 1 ? "n " : " ") + type;
  };
});
const deprecatedWarnings = {};
validators.transitional = function transitional(validator2, version, message) {
  function formatMessage(opt, desc) {
    return "[Axios v" + VERSION + "] Transitional option '" + opt + "'" + desc + (message ? ". " + message : "");
  }
  return (value, opt, opts) => {
    if (validator2 === false) {
      throw new AxiosError(formatMessage(opt, " has been removed" + (version ? " in " + version : "")), AxiosError.ERR_DEPRECATED);
    }
    if (version && !deprecatedWarnings[opt]) {
      deprecatedWarnings[opt] = true;
      console.warn(formatMessage(opt, " has been deprecated since v" + version + " and will be removed in the near future"));
    }
    return validator2 ? validator2(value, opt, opts) : true;
  };
};
function assertOptions(options, schema, allowUnknown) {
  if (typeof options !== "object") {
    throw new AxiosError("options must be an object", AxiosError.ERR_BAD_OPTION_VALUE);
  }
  const keys = Object.keys(options);
  let i = keys.length;
  while (i-- > 0) {
    const opt = keys[i];
    const validator2 = schema[opt];
    if (validator2) {
      const value = options[opt];
      const result = value === void 0 || validator2(value, opt, options);
      if (result !== true) {
        throw new AxiosError("option " + opt + " must be " + result, AxiosError.ERR_BAD_OPTION_VALUE);
      }
      continue;
    }
    if (allowUnknown !== true) {
      throw new AxiosError("Unknown option " + opt, AxiosError.ERR_BAD_OPTION);
    }
  }
}
var validator = {
  assertOptions,
  validators
};
const validators$1 = validator.validators;
class Axios {
  constructor(instanceConfig) {
    this.defaults = instanceConfig;
    this.interceptors = {
      request: new InterceptorManager(),
      response: new InterceptorManager()
    };
  }
  request(configOrUrl, config) {
    if (typeof configOrUrl === "string") {
      config = config || {};
      config.url = configOrUrl;
    } else {
      config = configOrUrl || {};
    }
    config = mergeConfig(this.defaults, config);
    const {transitional: transitional2, paramsSerializer, headers} = config;
    if (transitional2 !== void 0) {
      validator.assertOptions(transitional2, {
        silentJSONParsing: validators$1.transitional(validators$1.boolean),
        forcedJSONParsing: validators$1.transitional(validators$1.boolean),
        clarifyTimeoutError: validators$1.transitional(validators$1.boolean)
      }, false);
    }
    if (paramsSerializer != null) {
      if (utils.isFunction(paramsSerializer)) {
        config.paramsSerializer = {
          serialize: paramsSerializer
        };
      } else {
        validator.assertOptions(paramsSerializer, {
          encode: validators$1.function,
          serialize: validators$1.function
        }, true);
      }
    }
    config.method = (config.method || this.defaults.method || "get").toLowerCase();
    let contextHeaders;
    contextHeaders = headers && utils.merge(headers.common, headers[config.method]);
    contextHeaders && utils.forEach(["delete", "get", "head", "post", "put", "patch", "common"], (method) => {
      delete headers[method];
    });
    config.headers = AxiosHeaders.concat(contextHeaders, headers);
    const requestInterceptorChain = [];
    let synchronousRequestInterceptors = true;
    this.interceptors.request.forEach(function unshiftRequestInterceptors(interceptor) {
      if (typeof interceptor.runWhen === "function" && interceptor.runWhen(config) === false) {
        return;
      }
      synchronousRequestInterceptors = synchronousRequestInterceptors && interceptor.synchronous;
      requestInterceptorChain.unshift(interceptor.fulfilled, interceptor.rejected);
    });
    const responseInterceptorChain = [];
    this.interceptors.response.forEach(function pushResponseInterceptors(interceptor) {
      responseInterceptorChain.push(interceptor.fulfilled, interceptor.rejected);
    });
    let promise;
    let i = 0;
    let len;
    if (!synchronousRequestInterceptors) {
      const chain = [dispatchRequest.bind(this), void 0];
      chain.unshift.apply(chain, requestInterceptorChain);
      chain.push.apply(chain, responseInterceptorChain);
      len = chain.length;
      promise = Promise.resolve(config);
      while (i < len) {
        promise = promise.then(chain[i++], chain[i++]);
      }
      return promise;
    }
    len = requestInterceptorChain.length;
    let newConfig = config;
    i = 0;
    while (i < len) {
      const onFulfilled = requestInterceptorChain[i++];
      const onRejected = requestInterceptorChain[i++];
      try {
        newConfig = onFulfilled(newConfig);
      } catch (error) {
        onRejected.call(this, error);
        break;
      }
    }
    try {
      promise = dispatchRequest.call(this, newConfig);
    } catch (error) {
      return Promise.reject(error);
    }
    i = 0;
    len = responseInterceptorChain.length;
    while (i < len) {
      promise = promise.then(responseInterceptorChain[i++], responseInterceptorChain[i++]);
    }
    return promise;
  }
  getUri(config) {
    config = mergeConfig(this.defaults, config);
    const fullPath = buildFullPath(config.baseURL, config.url);
    return buildURL(fullPath, config.params, config.paramsSerializer);
  }
}
utils.forEach(["delete", "get", "head", "options"], function forEachMethodNoData2(method) {
  Axios.prototype[method] = function(url, config) {
    return this.request(mergeConfig(config || {}, {
      method,
      url,
      data: (config || {}).data
    }));
  };
});
utils.forEach(["post", "put", "patch"], function forEachMethodWithData2(method) {
  function generateHTTPMethod(isForm) {
    return function httpMethod(url, data, config) {
      return this.request(mergeConfig(config || {}, {
        method,
        headers: isForm ? {
          "Content-Type": "multipart/form-data"
        } : {},
        url,
        data
      }));
    };
  }
  Axios.prototype[method] = generateHTTPMethod();
  Axios.prototype[method + "Form"] = generateHTTPMethod(true);
});
class CancelToken {
  constructor(executor) {
    if (typeof executor !== "function") {
      throw new TypeError("executor must be a function.");
    }
    let resolvePromise;
    this.promise = new Promise(function promiseExecutor(resolve) {
      resolvePromise = resolve;
    });
    const token = this;
    this.promise.then((cancel) => {
      if (!token._listeners)
        return;
      let i = token._listeners.length;
      while (i-- > 0) {
        token._listeners[i](cancel);
      }
      token._listeners = null;
    });
    this.promise.then = (onfulfilled) => {
      let _resolve;
      const promise = new Promise((resolve) => {
        token.subscribe(resolve);
        _resolve = resolve;
      }).then(onfulfilled);
      promise.cancel = function reject() {
        token.unsubscribe(_resolve);
      };
      return promise;
    };
    executor(function cancel(message, config, request) {
      if (token.reason) {
        return;
      }
      token.reason = new CanceledError(message, config, request);
      resolvePromise(token.reason);
    });
  }
  throwIfRequested() {
    if (this.reason) {
      throw this.reason;
    }
  }
  subscribe(listener) {
    if (this.reason) {
      listener(this.reason);
      return;
    }
    if (this._listeners) {
      this._listeners.push(listener);
    } else {
      this._listeners = [listener];
    }
  }
  unsubscribe(listener) {
    if (!this._listeners) {
      return;
    }
    const index = this._listeners.indexOf(listener);
    if (index !== -1) {
      this._listeners.splice(index, 1);
    }
  }
  static source() {
    let cancel;
    const token = new CancelToken(function executor(c) {
      cancel = c;
    });
    return {
      token,
      cancel
    };
  }
}
function spread(callback) {
  return function wrap(arr) {
    return callback.apply(null, arr);
  };
}
function isAxiosError(payload) {
  return utils.isObject(payload) && payload.isAxiosError === true;
}
const HttpStatusCode = {
  Continue: 100,
  SwitchingProtocols: 101,
  Processing: 102,
  EarlyHints: 103,
  Ok: 200,
  Created: 201,
  Accepted: 202,
  NonAuthoritativeInformation: 203,
  NoContent: 204,
  ResetContent: 205,
  PartialContent: 206,
  MultiStatus: 207,
  AlreadyReported: 208,
  ImUsed: 226,
  MultipleChoices: 300,
  MovedPermanently: 301,
  Found: 302,
  SeeOther: 303,
  NotModified: 304,
  UseProxy: 305,
  Unused: 306,
  TemporaryRedirect: 307,
  PermanentRedirect: 308,
  BadRequest: 400,
  Unauthorized: 401,
  PaymentRequired: 402,
  Forbidden: 403,
  NotFound: 404,
  MethodNotAllowed: 405,
  NotAcceptable: 406,
  ProxyAuthenticationRequired: 407,
  RequestTimeout: 408,
  Conflict: 409,
  Gone: 410,
  LengthRequired: 411,
  PreconditionFailed: 412,
  PayloadTooLarge: 413,
  UriTooLong: 414,
  UnsupportedMediaType: 415,
  RangeNotSatisfiable: 416,
  ExpectationFailed: 417,
  ImATeapot: 418,
  MisdirectedRequest: 421,
  UnprocessableEntity: 422,
  Locked: 423,
  FailedDependency: 424,
  TooEarly: 425,
  UpgradeRequired: 426,
  PreconditionRequired: 428,
  TooManyRequests: 429,
  RequestHeaderFieldsTooLarge: 431,
  UnavailableForLegalReasons: 451,
  InternalServerError: 500,
  NotImplemented: 501,
  BadGateway: 502,
  ServiceUnavailable: 503,
  GatewayTimeout: 504,
  HttpVersionNotSupported: 505,
  VariantAlsoNegotiates: 506,
  InsufficientStorage: 507,
  LoopDetected: 508,
  NotExtended: 510,
  NetworkAuthenticationRequired: 511
};
Object.entries(HttpStatusCode).forEach(([key, value]) => {
  HttpStatusCode[value] = key;
});
function createInstance(defaultConfig) {
  const context = new Axios(defaultConfig);
  const instance = bind(Axios.prototype.request, context);
  utils.extend(instance, Axios.prototype, context, {allOwnKeys: true});
  utils.extend(instance, context, null, {allOwnKeys: true});
  instance.create = function create(instanceConfig) {
    return createInstance(mergeConfig(defaultConfig, instanceConfig));
  };
  return instance;
}
const axios = createInstance(defaults);
axios.Axios = Axios;
axios.CanceledError = CanceledError;
axios.CancelToken = CancelToken;
axios.isCancel = isCancel;
axios.VERSION = VERSION;
axios.toFormData = toFormData;
axios.AxiosError = AxiosError;
axios.Cancel = axios.CanceledError;
axios.all = function all(promises) {
  return Promise.all(promises);
};
axios.spread = spread;
axios.isAxiosError = isAxiosError;
axios.mergeConfig = mergeConfig;
axios.AxiosHeaders = AxiosHeaders;
axios.formToJSON = (thing) => formDataToJSON(utils.isHTMLForm(thing) ? new FormData(thing) : thing);
axios.HttpStatusCode = HttpStatusCode;
axios.default = axios;

/* generated by Svelte v3.58.0 */

function create_if_block_5(ctx) {
	let div;
	let t_value = /*form*/ ctx[1].error_message + "";
	let t;
	let div_intro;

	return {
		c() {
			div = element("div");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t = claim_text(div_nodes, t_value);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "message error svelte-atbrdi");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*form*/ 2 && t_value !== (t_value = /*form*/ ctx[1].error_message + "")) set_data(t, t_value);
		},
		i(local) {
			if (!div_intro) {
				add_render_callback(() => {
					div_intro = create_in_transition(div, fade, {});
					div_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (180:22) 
function create_if_block_4$1(ctx) {
	let div;
	let t_value = /*form*/ ctx[1].success_message + "";
	let t;
	let div_intro;

	return {
		c() {
			div = element("div");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t = claim_text(div_nodes, t_value);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "message svelte-atbrdi");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*form*/ 2 && t_value !== (t_value = /*form*/ ctx[1].success_message + "")) set_data(t, t_value);
		},
		i(local) {
			if (!div_intro) {
				add_render_callback(() => {
					div_intro = create_in_transition(div, fade, {});
					div_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (167:2) {#if !submitted && !error}
function create_if_block_2$1(ctx) {
	let form_1;
	let label;
	let input;
	let input_placeholder_value;
	let t;
	let button;
	let current_block_type_index;
	let if_block;
	let current;
	let mounted;
	let dispose;
	const if_block_creators = [create_if_block_3$1, create_else_block$1];
	const if_blocks = [];

	function select_block_type_1(ctx, dirty) {
		if (!/*submitting*/ ctx[3]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type_1(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			form_1 = element("form");
			label = element("label");
			input = element("input");
			t = space();
			button = element("button");
			if_block.c();
			this.h();
		},
		l(nodes) {
			form_1 = claim_element(nodes, "FORM", { class: true });
			var form_1_nodes = children(form_1);
			label = claim_element(form_1_nodes, "LABEL", { class: true });
			var label_nodes = children(label);

			input = claim_element(label_nodes, "INPUT", {
				name: true,
				type: true,
				placeholder: true,
				class: true
			});

			label_nodes.forEach(detach);
			t = claim_space(form_1_nodes);
			button = claim_element(form_1_nodes, "BUTTON", { class: true, type: true });
			var button_nodes = children(button);
			if_block.l(button_nodes);
			button_nodes.forEach(detach);
			form_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			input.required = true;
			attr(input, "name", "email");
			attr(input, "type", "text");
			attr(input, "placeholder", input_placeholder_value = /*form*/ ctx[1].placeholder);
			attr(input, "class", "svelte-atbrdi");
			attr(label, "class", "svelte-atbrdi");
			attr(button, "class", "button svelte-atbrdi");
			attr(button, "type", "submit");
			attr(form_1, "class", "svelte-atbrdi");
		},
		m(target, anchor) {
			insert_hydration(target, form_1, anchor);
			append_hydration(form_1, label);
			append_hydration(label, input);
			append_hydration(form_1, t);
			append_hydration(form_1, button);
			if_blocks[current_block_type_index].m(button, null);
			current = true;

			if (!mounted) {
				dispose = listen(form_1, "submit", prevent_default(/*submit_form*/ ctx[6]));
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty & /*form*/ 2 && input_placeholder_value !== (input_placeholder_value = /*form*/ ctx[1].placeholder)) {
				attr(input, "placeholder", input_placeholder_value);
			}

			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type_1(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(button, null);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(form_1);
			if_blocks[current_block_type_index].d();
			mounted = false;
			dispose();
		}
	};
}

// (175:8) {:else}
function create_else_block$1(ctx) {
	let icon;
	let current;
	icon = new Component$1({ props: { icon: "eos-icons:loading" } });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (173:8) {#if !submitting}
function create_if_block_3$1(ctx) {
	let t_value = /*form*/ ctx[1].button_label + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*form*/ 2 && t_value !== (t_value = /*form*/ ctx[1].button_label + "")) set_data(t, t_value);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (185:2) {#if graphics.left}
function create_if_block_1$2(ctx) {
	let div;
	let raw_value = /*graphics*/ ctx[2].left + "";

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "graphic left svelte-atbrdi");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			div.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*graphics*/ 4 && raw_value !== (raw_value = /*graphics*/ ctx[2].left + "")) div.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (188:2) {#if graphics.right}
function create_if_block$3(ctx) {
	let div;
	let raw_value = /*graphics*/ ctx[2].right + "";

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "graphic right svelte-atbrdi");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			div.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*graphics*/ 4 && raw_value !== (raw_value = /*graphics*/ ctx[2].right + "")) div.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$3(ctx) {
	let div1;
	let div0;
	let section;
	let h1;
	let t0;
	let t1;
	let current_block_type_index;
	let if_block0;
	let t2;
	let t3;
	let current;
	const if_block_creators = [create_if_block_2$1, create_if_block_4$1, create_if_block_5];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (!/*submitted*/ ctx[4] && !/*error*/ ctx[5]) return 0;
		if (/*submitted*/ ctx[4]) return 1;
		if (/*error*/ ctx[5]) return 2;
		return -1;
	}

	if (~(current_block_type_index = select_block_type(ctx))) {
		if_block0 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	}

	let if_block1 = /*graphics*/ ctx[2].left && create_if_block_1$2(ctx);
	let if_block2 = /*graphics*/ ctx[2].right && create_if_block$3(ctx);

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			section = element("section");
			h1 = element("h1");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			if (if_block0) if_block0.c();
			t2 = space();
			if (if_block1) if_block1.c();
			t3 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			section = claim_element(div0_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h1 = claim_element(section_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*heading*/ ctx[0]);
			h1_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			if (if_block0) if_block0.l(section_nodes);
			t2 = claim_space(section_nodes);
			if (if_block1) if_block1.l(section_nodes);
			t3 = claim_space(section_nodes);
			if (if_block2) if_block2.l(section_nodes);
			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "headline svelte-atbrdi");
			attr(section, "class", "section-container svelte-atbrdi");
			attr(div0, "class", "component svelte-atbrdi");
			attr(div1, "class", "section svelte-atbrdi");
			attr(div1, "id", "section-63754163-a178-485f-85fd-86b46c47a959");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, section);
			append_hydration(section, h1);
			append_hydration(h1, t0);
			append_hydration(section, t1);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].m(section, null);
			}

			append_hydration(section, t2);
			if (if_block1) if_block1.m(section, null);
			append_hydration(section, t3);
			if (if_block2) if_block2.m(section, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if (~current_block_type_index) {
					if_blocks[current_block_type_index].p(ctx, dirty);
				}
			} else {
				if (if_block0) {
					group_outros();

					transition_out(if_blocks[previous_block_index], 1, 1, () => {
						if_blocks[previous_block_index] = null;
					});

					check_outros();
				}

				if (~current_block_type_index) {
					if_block0 = if_blocks[current_block_type_index];

					if (!if_block0) {
						if_block0 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
						if_block0.c();
					} else {
						if_block0.p(ctx, dirty);
					}

					transition_in(if_block0, 1);
					if_block0.m(section, t2);
				} else {
					if_block0 = null;
				}
			}

			if (/*graphics*/ ctx[2].left) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_1$2(ctx);
					if_block1.c();
					if_block1.m(section, t3);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}

			if (/*graphics*/ ctx[2].right) {
				if (if_block2) {
					if_block2.p(ctx, dirty);
				} else {
					if_block2 = create_if_block$3(ctx);
					if_block2.c();
					if_block2.m(section, null);
				}
			} else if (if_block2) {
				if_block2.d(1);
				if_block2 = null;
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block0);
			current = true;
		},
		o(local) {
			transition_out(if_block0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].d();
			}

			if (if_block1) if_block1.d();
			if (if_block2) if_block2.d();
		}
	};
}

function get_form_data(form) {
	const form_data = new FormData(form);
	var object = {};

	form_data.forEach((value, key) => {
		object[key] = value;
	});

	return object;
}

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { image } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { form } = $$props;
	let { graphics } = $$props;
	let submitting = false;
	let submitted = false;
	let error = false;

	async function submit_form(e) {
		$$invalidate(3, submitting = true);
		const form_data = get_form_data(e.target);
		const { status } = await axios.post(form.endpoint, form_data).catch(e => ({ status: 400 }));

		if (status === 200) {
			$$invalidate(4, submitted = true);
		} else {
			$$invalidate(5, error = true);
		}
	}

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(7, favicon = $$props.favicon);
		if ('image' in $$props) $$invalidate(8, image = $$props.image);
		if ('title' in $$props) $$invalidate(9, title = $$props.title);
		if ('description' in $$props) $$invalidate(10, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('form' in $$props) $$invalidate(1, form = $$props.form);
		if ('graphics' in $$props) $$invalidate(2, graphics = $$props.graphics);
	};

	return [
		heading,
		form,
		graphics,
		submitting,
		submitted,
		error,
		submit_form,
		favicon,
		image,
		title,
		description
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 7,
			image: 8,
			title: 9,
			description: 10,
			heading: 0,
			form: 1,
			graphics: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i];
	child_ctx[8] = i;
	return child_ctx;
}

// (105:8) {#if item.thumbnail.url}
function create_if_block$4(ctx) {
	let img;
	let img_data_key_value;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", {
				"data-key": true,
				src: true,
				alt: true,
				class: true
			});

			this.h();
		},
		h() {
			attr(img, "data-key", img_data_key_value = "items[" + /*i*/ ctx[8] + "].thumbnail");
			if (!src_url_equal(img.src, img_src_value = /*item*/ ctx[6].thumbnail.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*item*/ ctx[6].thumbnail.alt);
			attr(img, "class", "svelte-di9dxy");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 2 && !src_url_equal(img.src, img_src_value = /*item*/ ctx[6].thumbnail.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*items*/ 2 && img_alt_value !== (img_alt_value = /*item*/ ctx[6].thumbnail.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (88:4) {#each items as item, i}
function create_each_block$1(ctx) {
	let li;
	let div1;
	let a;
	let t0_value = /*item*/ ctx[6].link.label + "";
	let t0;
	let a_href_value;
	let t1;
	let div0;
	let raw_value = /*item*/ ctx[6].description.html + "";
	let t2;
	let span;
	let t3_value = /*item*/ ctx[6].date + "";
	let t3;
	let t4;
	let t5;
	let if_block = /*item*/ ctx[6].thumbnail.url && create_if_block$4(ctx);

	return {
		c() {
			li = element("li");
			div1 = element("div");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			div0 = element("div");
			t2 = space();
			span = element("span");
			t3 = text(t3_value);
			t4 = space();
			if (if_block) if_block.c();
			t5 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div1 = claim_element(li_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a = claim_element(div1_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			span = claim_element(div1_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t3 = claim_text(span_nodes, t3_value);
			span_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(li_nodes);
			if (if_block) if_block.l(li_nodes);
			t5 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "title svelte-di9dxy");
			attr(a, "href", a_href_value = /*item*/ ctx[6].link.url);
			attr(div0, "class", "description svelte-di9dxy");
			attr(span, "class", "date svelte-di9dxy");
			attr(div1, "class", "post-info");
			attr(li, "class", "svelte-di9dxy");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div1);
			append_hydration(div1, a);
			append_hydration(a, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div1, t2);
			append_hydration(div1, span);
			append_hydration(span, t3);
			append_hydration(li, t4);
			if (if_block) if_block.m(li, null);
			append_hydration(li, t5);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 2 && t0_value !== (t0_value = /*item*/ ctx[6].link.label + "")) set_data(t0, t0_value);

			if (dirty & /*items*/ 2 && a_href_value !== (a_href_value = /*item*/ ctx[6].link.url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*items*/ 2 && raw_value !== (raw_value = /*item*/ ctx[6].description.html + "")) div0.innerHTML = raw_value;			if (dirty & /*items*/ 2 && t3_value !== (t3_value = /*item*/ ctx[6].date + "")) set_data(t3, t3_value);

			if (/*item*/ ctx[6].thumbnail.url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$4(ctx);
					if_block.c();
					if_block.m(li, t5);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		d(detaching) {
			if (detaching) detach(li);
			if (if_block) if_block.d();
		}
	};
}

function create_fragment$4(ctx) {
	let div1;
	let div0;
	let section;
	let h2;
	let t0;
	let t1;
	let ul;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			section = claim_element(div0_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "svelte-di9dxy");
			attr(ul, "class", "items svelte-di9dxy");
			attr(section, "class", "section-container svelte-di9dxy");
			attr(div0, "class", "component");
			attr(div1, "class", "section");
			attr(div1, "id", "section-6eeaaa91-2985-4785-97a2-5dd44b6ec00e");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { image } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('image' in $$props) $$invalidate(3, image = $$props.image);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('description' in $$props) $$invalidate(5, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
	};

	return [heading, items, favicon, image, title, description];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 2,
			image: 3,
			title: 4,
			description: 5,
			heading: 0,
			items: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	child_ctx[8] = list[i].icon;
	return child_ctx;
}

// (74:8) {#each social_links as {link, icon}}
function create_each_block$2(ctx) {
	let li;
	let a;
	let icon;
	let a_href_value;
	let a_aria_label_value;
	let t;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[8] } });

	return {
		c() {
			li = element("li");
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);

			a = claim_element(li_nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			a_nodes.forEach(detach);
			t = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
			attr(a, "aria-label", a_aria_label_value = /*icon*/ ctx[8]);
			attr(a, "class", "svelte-1excgdw");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			mount_component(icon, a, null);
			append_hydration(li, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social_links*/ 1) icon_changes.icon = /*icon*/ ctx[8];
			icon.$set(icon_changes);

			if (!current || dirty & /*social_links*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social_links*/ 1 && a_aria_label_value !== (a_aria_label_value = /*icon*/ ctx[8])) {
				attr(a, "aria-label", a_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$5(ctx) {
	let div3;
	let div2;
	let footer;
	let div1;
	let hr;
	let t0;
	let div0;
	let span0;
	let t1;
	let t2_value = new Date().getFullYear() + "";
	let t2;
	let t3;
	let span1;
	let a;
	let t4;
	let t5;
	let t6;
	let ul;
	let current;
	let each_value = /*social_links*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			footer = element("footer");
			div1 = element("div");
			hr = element("hr");
			t0 = space();
			div0 = element("div");
			span0 = element("span");
			t1 = text("Copyright ");
			t2 = text(t2_value);
			t3 = space();
			span1 = element("span");
			a = element("a");
			t4 = text("Primo");
			t5 = text(" Powered");
			t6 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			footer = claim_element(div2_nodes, "FOOTER", {});
			var footer_nodes = children(footer);
			div1 = claim_element(footer_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			hr = claim_element(div1_nodes, "HR", { class: true });
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t1 = claim_text(span0_nodes, "Copyright ");
			t2 = claim_text(span0_nodes, t2_value);
			span0_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			a = claim_element(span1_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t4 = claim_text(a_nodes, "Primo");
			a_nodes.forEach(detach);
			t5 = claim_text(span1_nodes, " Powered");
			span1_nodes.forEach(detach);
			t6 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(hr, "class", "svelte-1excgdw");
			attr(span0, "class", "copyright svelte-1excgdw");
			attr(a, "href", "https://primo.so");
			attr(a, "class", "svelte-1excgdw");
			attr(span1, "class", "primo svelte-1excgdw");
			attr(ul, "class", "svelte-1excgdw");
			attr(div0, "class", "footer svelte-1excgdw");
			attr(div1, "class", "section-container svelte-1excgdw");
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-13765790-eafd-4138-b734-4b00d06854ef");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, footer);
			append_hydration(footer, div1);
			append_hydration(div1, hr);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t1);
			append_hydration(span0, t2);
			append_hydration(div0, t3);
			append_hydration(div0, span1);
			append_hydration(span1, a);
			append_hydration(a, t4);
			append_hydration(span1, t5);
			append_hydration(div0, t6);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (dirty & /*social_links*/ 1) {
				each_value = /*social_links*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { image } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { email } = $$props;
	let { social_links } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(1, favicon = $$props.favicon);
		if ('image' in $$props) $$invalidate(2, image = $$props.image);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('heading' in $$props) $$invalidate(5, heading = $$props.heading);
		if ('email' in $$props) $$invalidate(6, email = $$props.email);
		if ('social_links' in $$props) $$invalidate(0, social_links = $$props.social_links);
	};

	return [social_links, favicon, image, title, description, heading, email];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			favicon: 1,
			image: 2,
			title: 3,
			description: 4,
			heading: 5,
			email: 6,
			social_links: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function instance$6($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { image } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('image' in $$props) $$invalidate(1, image = $$props.image);
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('description' in $$props) $$invalidate(3, description = $$props.description);
	};

	return [favicon, image, title, description];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, null, safe_not_equal, {
			favicon: 0,
			image: 1,
			title: 2,
			description: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let current;

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png"
				},
				image: { "alt": "", "url": "" },
				title: "Blog",
				description: ""
			}
		});

	component_1 = new Component$2({
			props: {
				favicon: {
					"alt": "",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png"
				},
				image: { "alt": "", "url": "" },
				title: "Blog",
				description: "",
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "corta"
				},
				site_nav: [
					{
						"link": {
							"url": "http://localhost:5173/",
							"label": "Home"
						}
					},
					{
						"link": {
							"url": "http://localhost:5173/article-list",
							"label": "Blog"
						}
					},
					{
						"link": {
							"url": "http://localhost:5173/article-list",
							"label": "About"
						}
					}
				]
			}
		});

	component_2 = new Component$3({
			props: {
				favicon: {
					"alt": "",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png"
				},
				image: { "alt": "", "url": "" },
				title: "Blog",
				description: "",
				heading: "a blog about things I care about",
				form: {
					"endpoint": "https://formsubmit.co/your@email.com",
					"placeholder": "Email address",
					"button_label": "Subscribe",
					"error_message": "Uh oh, something wen't wrong.",
					"success_message": "Thanks for signing up! I promise not to spam you :)"
				},
				graphics: {
					"left": "<svg width=\"96\" height=\"97\" viewBox=\"0 0 96 97\" fill=\"none\" xmlns=\"http://www.w3.org/2000/svg\"> <path d=\"M41.77 25.6934C42.2372 23.7604 42.3973 21.7632 42.2437 19.7796C41.9374 15.7928 40.3716 11.8749 37.5242 8.70007C30.7898 1.19149 19.4274 0.680531 12.1477 7.55891C4.86607 14.4389 4.42549 26.1019 11.1599 33.6103C13.9997 36.7766 17.6618 38.6978 21.4931 39.3478C23.4158 39.6724 25.3808 39.6776 27.306 39.3563\" fill=\"#E1F4F9\"/> <path d=\"M43.3261 22.0097C43.2758 23.3377 43.0931 24.6578 42.7794 25.9554L40.7604 25.4313C41.2017 23.6065 41.3519 21.7318 41.2068 19.8589C40.9053 15.9373 39.368 12.3282 36.7607 9.42138C33.6923 6.00021 29.5156 4.00437 25.0002 3.80132C20.4846 3.59826 16.171 5.21229 12.854 8.34632C6.00649 14.8164 5.58881 25.8261 11.9234 32.8887C14.5211 35.7851 17.8872 37.6543 21.6579 38.2941C23.4799 38.6018 25.3228 38.6045 27.1343 38.3023L27.4777 40.4107C25.4434 40.7501 23.3748 40.7471 21.3291 40.4016C17.0934 39.6829 13.3131 37.5839 10.3961 34.3316C3.28259 26.4002 3.7516 14.0369 11.4412 6.77126C15.1661 3.25178 20.0101 1.43929 25.0809 1.66732C30.1517 1.89535 34.8419 4.1368 38.2877 7.97853C41.2155 11.2429 42.9421 15.2963 43.2806 19.7007C43.3401 20.471 43.3553 21.2417 43.3261 22.0097Z\" fill=\"#333333\"/> <path d=\"M17.1008 8.59328C17.0882 8.92496 16.9258 9.24476 16.6359 9.44082C16.0266 9.85234 15.4434 10.3202 14.9026 10.8312C14.0163 11.6686 13.2454 12.6185 12.6111 13.6546C12.3061 14.153 11.664 14.3011 11.1772 13.9855C10.6904 13.6696 10.5432 13.0098 10.848 12.5115C11.58 11.3159 12.4687 10.2206 13.4897 9.25593C14.1126 8.66757 14.7843 8.12886 15.4866 7.65439C15.9656 7.33086 16.6112 7.4687 16.9284 7.96188C17.0535 8.1565 17.109 8.3775 17.1008 8.59328Z\" fill=\"white\"/> <path d=\"M35.8424 10.9673C35.832 11.2393 35.7204 11.5066 35.5099 11.7051C35.0887 12.102 34.4315 12.0725 34.0421 11.6393C30.2715 7.44694 24.2698 6.0181 19.1079 8.08375C18.5746 8.29719 17.971 8.0266 17.76 7.47942C17.549 6.93182 17.8103 6.31535 18.3436 6.10212C21.2425 4.9421 24.3905 4.6988 27.4477 5.39851C30.5771 6.11465 33.3847 7.77578 35.5672 10.2025C35.7617 10.419 35.8527 10.6953 35.8424 10.9673Z\" fill=\"white\"/> <path d=\"M22.1274 32.5825C22.1937 30.7952 20.8332 29.281 19.0885 29.2005C17.3439 29.12 15.8759 30.5037 15.8096 32.291C15.7433 34.0783 17.1038 35.5925 18.8484 35.673C20.593 35.7535 22.0611 34.3698 22.1274 32.5825Z\" fill=\"#F9E33D\"/> <path d=\"M38.8437 16.7051C38.91 14.9178 37.5495 13.4036 35.8049 13.3231C34.0602 13.2426 32.5922 14.6263 32.5259 16.4136C32.4596 18.2009 33.8201 19.715 35.5647 19.7955C37.3093 19.876 38.7774 18.4924 38.8437 16.7051Z\" fill=\"#F9E33D\"/> <path d=\"M23.1676 32.6305C23.125 33.7796 22.6482 34.8397 21.8249 35.6158C20.1253 37.2175 17.4614 37.0946 15.8864 35.3418C15.1235 34.4925 14.7266 33.3921 14.7693 32.243C14.8119 31.0939 15.2887 30.0338 16.1122 29.2579C16.9354 28.482 18.0064 28.083 19.1283 28.1348C20.2499 28.1866 21.2877 28.6828 22.0509 29.5319C22.8134 30.381 23.2102 31.4814 23.1676 32.6305ZM16.8496 32.339C16.8281 32.9187 17.0282 33.4739 17.4133 33.9025C18.2079 34.7868 19.5521 34.8488 20.4095 34.0407C20.8248 33.6493 21.0653 33.1145 21.0869 32.5345C21.1084 31.9547 20.9083 31.3995 20.5234 30.9712C20.1385 30.5427 19.6149 30.2924 19.049 30.2663C18.4831 30.2402 17.9427 30.4413 17.5272 30.833C17.1117 31.2244 16.8711 31.7594 16.8496 32.339Z\" fill=\"#666666\"/> <path d=\"M39.8821 16.7534C39.8412 17.8552 39.3911 18.9376 38.5413 19.7386C37.7178 20.5145 36.6468 20.9135 35.5252 20.8617C34.4035 20.81 33.3657 20.3137 32.6028 19.4646C31.8398 18.6155 31.443 17.5151 31.4856 16.366C31.5282 15.2169 32.0052 14.1569 32.8285 13.3807C34.5279 11.779 37.1918 11.9019 38.767 13.6547C39.5544 14.531 39.9229 15.6519 39.8821 16.7534ZM33.5661 16.462C33.5446 17.0418 33.7447 17.5969 34.1296 18.0253C34.5147 18.4539 35.0383 18.7041 35.6042 18.7302C36.1701 18.7563 36.7105 18.5552 37.126 18.1635C37.9834 17.3552 38.0347 15.9783 37.2399 15.094C36.4453 14.2097 35.1011 14.1477 34.2437 14.9558C33.8282 15.3472 33.5877 15.882 33.5661 16.462Z\" fill=\"#666666\"/> <path d=\"M35.26 34.8565C30.7837 39.0859 23.7733 38.7706 19.6327 34.1537L17.0327 31.2549C12.8919 26.638 13.165 19.4414 17.6411 15.212L19.1098 13.8242C23.5861 9.59485 30.5965 9.9101 34.7372 14.527L37.3371 17.4258C41.4779 22.0427 41.2048 29.2393 36.7287 33.4687L35.26 34.8565Z\" fill=\"#8FCDF7\"/> <path d=\"M33.7651 82.1846L34.9608 83.5177C35.6166 84.2489 36.721 84.2985 37.4284 83.6304L36.2934 79.3564L33.7651 82.1846Z\" fill=\"#F9763D\"/> <path d=\"M91.6131 67.9771L83.6665 75.4846L82.5696 72.4125L85.9415 69.2268L91.6131 67.9771Z\" fill=\"#F9763D\"/> <path d=\"M76.7564 54.0567C77.2605 54.5916 78.0109 55.4181 78.8766 56.4716L73.7927 61.2752L73.791 61.2769C73.2111 60.7728 72.6081 60.2873 71.9836 59.8318C73.6369 57.9649 75.2288 56.0399 76.7564 54.0567Z\" fill=\"#158ACC\"/> <path d=\"M73.7831 61.2754L78.8664 56.4724C79.5622 57.316 80.3301 58.3045 81.1052 59.4029L76.4105 63.8386C75.5986 62.9605 74.7195 62.0924 73.7813 61.277L73.7831 61.2754Z\" fill=\"#53AEF9\"/> <path d=\"M76.3991 63.8392L81.0944 59.4028C81.7774 60.3714 82.4652 61.4269 83.1125 62.5423L78.7716 66.6438C78.0624 65.7345 77.269 64.782 76.3991 63.8392Z\" fill=\"#53AEF9\"/> <path d=\"M78.7594 66.6455L83.1011 62.5433C83.7289 63.6304 84.3197 64.7779 84.8262 65.9605L80.9131 69.6578C80.3317 68.7752 79.6079 67.7409 78.7594 66.6455Z\" fill=\"#53AEF9\"/> <path d=\"M80.9018 69.6599L84.8157 65.9621C85.2729 67.0255 85.6637 68.1199 85.9556 69.2297L82.5808 72.4182C82.5808 72.418 81.9873 71.3014 80.9018 69.6599Z\" fill=\"#53AEF9\"/> <path d=\"M32.8259 17.4615L35.2846 20.2029C38.196 23.449 38.0047 28.4933 34.8575 31.467L33.4684 32.7794C30.3212 35.7531 25.4075 35.5321 22.4961 32.286L20.0375 29.5447C17.1261 26.2986 17.3174 21.2542 20.4646 18.2806L21.8537 16.9681C25.0011 13.9945 29.9145 14.2155 32.8259 17.4615Z\" fill=\"#D8B86F\"/> <path d=\"M30.7944 19.3813L33.253 22.1227C36.1644 25.3688 36.7841 29.6467 34.637 31.6756L33.6893 32.5709C31.542 34.5998 27.4395 33.6125 24.5281 30.3664L22.0695 27.625C19.1581 24.3789 18.5384 20.101 20.6855 18.0721L21.6332 17.1767C23.7803 15.1481 27.883 16.1352 30.7944 19.3813Z\" fill=\"#F7D789\"/> <path d=\"M69.0815 85.2486L71.9759 86.6252L64.0243 94.1382L65.7075 88.4365L69.0815 85.2486Z\" fill=\"#F9763D\"/> <path d=\"M69.0928 85.2469L65.7214 88.4318C64.6691 88.0422 63.6395 87.5524 62.6457 86.9976L66.5557 83.304C68.0586 84.5484 69.0928 85.2469 69.0928 85.2469Z\" fill=\"#53AEF9\"/> <path d=\"M51.7996 77.7335C53.8509 76.3352 55.8526 74.868 57.8013 73.3312C58.1919 74.0075 58.6133 74.6642 59.0548 75.2988L59.0531 75.3004L53.9704 80.1027C53.0191 79.1306 52.2772 78.2932 51.7996 77.7335Z\" fill=\"#158ACC\"/> <path d=\"M66.5654 83.3056L62.6546 87.0004C61.5486 86.3848 60.4839 85.6865 59.481 84.9551L63.82 80.8558C64.8128 81.8133 65.7568 82.6385 66.5654 83.3056Z\" fill=\"#53AEF9\"/> <path d=\"M59.0438 75.2999L59.0455 75.2983C59.7597 76.3252 60.53 77.2962 61.3155 78.1991L56.621 82.6348C55.6186 81.7513 54.7221 80.8842 53.9605 80.1028L59.0438 75.2999Z\" fill=\"#53AEF9\"/> <path d=\"M63.8307 80.8564L59.4911 84.9565C58.4617 84.2025 57.4942 83.4121 56.6104 82.6337L61.3043 78.1988C62.1474 79.1664 63.0064 80.0563 63.8307 80.8564Z\" fill=\"#53AEF9\"/> <path d=\"M65.7762 25.1981C65.5875 25.6497 65.3045 26.0739 64.9289 26.4289C63.5003 27.7787 61.2689 27.6769 59.9472 26.2032C59.0128 25.1614 58.7818 23.7092 59.2356 22.4705C57.2721 21.7542 55.5086 21.207 54.02 20.7892C50.8239 19.8969 48.8806 19.6137 48.8806 19.6137C48.242 19.4856 47.5922 19.4025 46.9405 19.3683L41.7655 20.0099C40.9358 20.2727 40.1238 20.6096 39.3359 21.0276L39.3341 21.0292C43.1863 25.7348 42.8013 32.7488 38.3703 36.9354C33.9412 41.1203 27.099 40.9348 22.8482 36.6059C22.379 37.3759 21.9813 38.1817 21.6558 39.0135L20.6054 44.2539C20.5866 44.9217 20.6136 45.5869 20.6819 46.2569C20.6819 46.2569 20.7978 48.2698 21.4003 51.6096C21.7151 53.3623 22.1657 55.4768 22.8046 57.859L24.1821 62.4632L24.1804 62.4649C26.1275 68.3456 29.1458 75.2305 33.8004 82.0697L35.146 80.5629L35.3003 80.3919L36.3274 79.2426C36.3274 79.2426 31.6281 69.7263 31.7858 63.0969L31.7996 63.1123L34.9869 66.666L47.4403 80.5512C48.9384 79.6318 50.414 78.6772 51.8641 77.6839C53.9157 76.2854 55.9176 74.8179 57.8666 73.281C60.4214 71.2691 62.8835 69.1404 65.2496 66.9046C67.6159 64.6689 69.8859 62.3261 72.0488 59.8807C73.7019 58.014 75.2939 56.0893 76.8211 54.1063C77.9022 52.7049 78.9509 51.2744 79.9691 49.8165C79.9708 49.8149 79.9708 49.8149 79.9723 49.8135L67.5189 35.9283L64.3316 32.3746L64.3224 32.3644C70.7706 32.7522 79.6161 38.3415 79.6161 38.3415L80.9954 37.2423L82.5696 35.9903C76.8539 31.121 70.9834 27.6505 65.7762 25.1981ZM56.7714 45.9359L45.588 56.5025L36.1832 46.0162L47.3666 35.4496L56.7714 45.9359Z\" fill=\"#44A1E0\"/> <path d=\"M62.721 26.049L62.7193 26.0506L58.3625 24.2613C56.1022 23.4111 54.0863 22.7758 52.4105 22.3088C52.3949 22.3049 52.3807 22.2993 52.365 22.2954C50.2727 21.7103 48.1189 21.3999 45.9519 21.3563L40.4558 21.2462C40.1928 21.3126 39.934 21.3875 39.6799 21.4738C41.9764 29.078 36.9015 41.4084 23.2498 36.9976C23.1465 37.2523 23.0508 37.5122 22.9646 37.7759L22.616 43.4051C22.4794 45.6253 22.6014 47.8554 22.9967 50.044C23.0009 50.0589 23.0034 50.0753 23.0059 50.0916C23.3207 51.8443 23.7713 53.9588 24.4102 56.3411L25.7877 60.9453L25.786 60.9469C27.7175 66.7829 30.7044 73.6061 35.2991 80.3921L36.3262 79.2427C36.3262 79.2427 31.6269 69.7265 31.7846 63.0971L36.1745 64.6825C36.2554 64.3927 49.5564 78.5508 49.5564 78.5508C50.8914 77.7855 52.2021 76.9866 53.4874 76.149C55.3068 74.97 57.0746 73.7236 58.7895 72.4078C60.7547 70.9028 62.6501 69.3063 64.4724 67.6286C64.7326 67.3891 64.991 67.1479 65.2482 66.905C65.5052 66.6622 65.7608 66.4176 66.0148 66.1713C67.7946 64.4458 69.501 62.6387 71.1248 60.753C72.544 59.1076 73.9019 57.4038 75.1969 55.6403C76.1133 54.3947 76.9972 53.1198 77.8505 51.8177C77.8523 51.816 77.8523 51.816 77.8538 51.8146L64.6244 37.0643C64.9149 37.0692 64.3133 32.3629 64.3133 32.3629L64.3165 32.3631C64.3196 32.3632 64.3196 32.3632 64.3212 32.365C65.4736 32.4348 66.7007 32.6693 67.943 33.009C68.0971 33.0519 68.251 33.0947 68.4051 33.1408C68.7601 33.2448 69.1134 33.3569 69.4664 33.4756C69.6704 33.5435 69.8726 33.6129 70.0734 33.6839C72.3714 34.5017 74.5842 35.5601 76.2992 36.4609C76.4409 36.5341 76.5764 36.6071 76.7089 36.6766C77.0358 36.8512 77.341 37.0182 77.6193 37.1758C77.736 37.2381 77.8465 37.3002 77.9523 37.3603C78.1358 37.4633 78.3054 37.5605 78.4608 37.6523C78.5152 37.6825 78.5649 37.7109 78.6132 37.7408C78.7126 37.7975 78.8029 37.8505 78.8882 37.9015C79.3543 38.1769 79.615 38.3421 79.615 38.3421L80.8159 37.3865C74.6062 32.1257 68.228 28.5067 62.721 26.049ZM56.0435 46.6223L46.3151 55.8142L36.9102 45.3281L46.6387 36.1362L56.0435 46.6223Z\" fill=\"#53AEF9\"/> <path d=\"M25.1594 55.7549L28.0282 58.9534L24.218 62.5533L24.2163 62.5549C23.7514 61.1503 23.3462 59.802 22.9955 58.5282C22.9409 58.3315 22.8895 58.1382 22.8395 57.9467L25.1594 55.7549Z\" fill=\"#F9E33D\"/> <path d=\"M65.8084 25.1049C65.6198 25.5559 65.3369 25.9797 64.9616 26.3344C63.534 27.6827 61.3041 27.5809 59.9832 26.1089C59.0495 25.0682 58.8186 23.6176 59.2722 22.3803C59.6903 22.5311 60.1194 22.6904 60.5574 22.86C62.2004 23.4912 63.9633 24.2319 65.8084 25.1049Z\" fill=\"#F9E33D\"/> <path d=\"M41.3031 25.6393C41.1825 28.8179 39.8838 31.9424 37.435 34.2564L35.9663 35.6442C31.0691 40.2712 23.3993 39.9263 18.8689 34.8753L16.269 31.9765C14.0778 29.5334 12.9402 26.36 13.0661 23.0414C13.0661 23.0412 13.0661 23.0414 13.0661 23.0414C13.1919 19.7229 14.5658 16.6626 16.9347 14.4244L18.4035 13.0366C23.3009 8.40958 30.9705 8.75448 35.5009 13.8055L38.1008 16.7043C40.3655 19.2298 41.4236 22.4616 41.3031 25.6393ZM15.145 23.1351C15.0407 25.8837 15.9822 28.5113 17.7962 30.5336L20.3962 33.4325C24.1474 37.615 30.4985 37.9006 34.5536 34.0691L36.0224 32.6814C40.0777 28.8497 40.325 22.3295 36.5735 18.1474L33.9736 15.2485C30.2223 11.066 23.8713 10.7804 19.8161 14.6119L18.3474 15.9997C16.3866 17.8524 15.2492 20.3866 15.145 23.1351Z\" fill=\"#666666\"/> <path d=\"M38.3824 25.9839C38.2909 28.3968 37.2901 30.6237 35.5639 32.2546L34.1748 33.5671C30.611 36.9344 25.0295 36.6834 21.7327 33.0076L19.274 30.2662C17.6772 28.4858 16.8482 26.1767 16.9396 23.7638C17.0311 21.3509 18.0322 19.124 19.7584 17.4932L21.1474 16.1808C24.7113 12.8135 30.2928 13.0645 33.5895 16.7403L36.0482 19.4816C37.6449 21.262 38.4739 23.5712 38.3824 25.9839ZM19.0186 23.8573C18.9487 25.7 19.5819 27.4635 20.8013 28.8232L23.26 31.5645C25.7778 34.3718 30.0406 34.5635 32.7624 31.9919L34.1515 30.6794C35.4697 29.4339 36.234 27.7331 36.3039 25.8904C36.3738 24.0477 35.7408 22.2841 34.5214 20.9245L32.0627 18.1832C29.5449 15.3759 25.2821 15.1842 22.5603 17.7558L21.1712 19.0683C19.8528 20.3138 19.0884 22.0146 19.0186 23.8573Z\" fill=\"#666666\"/> <path d=\"M70.1517 85.2939C70.1411 85.5748 70.0225 85.8419 69.8191 86.0342L66.4472 89.2195C66.1633 89.4877 65.7571 89.5714 65.3926 89.4364C64.3439 89.0483 63.2602 88.5432 62.1718 87.9353C61.102 87.3398 59.9983 86.6287 58.8923 85.8222C57.9052 85.099 56.9115 84.2979 55.9368 83.4394C55.0109 82.6235 54.0966 81.7536 53.2188 80.8533C52.2353 79.848 51.4699 78.982 51.0012 78.4328L52.5624 77.0302C53.0096 77.5544 53.7407 78.3814 54.6837 79.3453C55.5254 80.2085 56.4008 81.0414 57.2864 81.822C58.2138 82.6387 59.158 83.4001 60.0929 84.0848C61.1285 84.8401 62.1601 85.505 63.1573 86.0601C63.9514 86.5034 64.7385 86.8856 65.5057 87.2002L67.4621 85.3522C67.043 85.0349 66.5202 84.6259 65.9251 84.1332C64.9613 83.3378 64.0173 82.4951 63.1205 81.6301C62.1909 80.7279 61.3204 79.8123 60.5311 78.907C59.669 77.9162 58.8817 76.9099 58.19 75.9152C57.7145 75.2317 57.2766 74.5441 56.8885 73.872L57.7775 73.3336L58.544 72.6078C58.5935 72.6631 58.6388 72.7251 58.6759 72.7896C59.034 73.4097 59.4393 74.0457 59.8806 74.6802C60.5283 75.6116 61.2678 76.5563 62.0786 77.4882C62.8286 78.3484 63.6581 79.2207 64.5433 80.0799C65.3985 80.9048 66.3015 81.7107 67.2249 82.4727C68.6652 83.6654 69.6719 84.3493 69.6819 84.3559C69.9498 84.5372 70.1223 84.8349 70.149 85.1626C70.1525 85.2067 70.1534 85.2504 70.1517 85.2939Z\" fill=\"#333333\"/> <path d=\"M27.5161 27.0774C27.5057 27.3505 27.394 27.6189 27.1832 27.8182C26.7614 28.2168 26.1033 28.1872 25.7133 27.7521L22.7532 24.4517C22.363 24.0167 22.3886 23.3413 22.8104 22.9428C23.2322 22.5442 23.8903 22.5738 24.2803 23.0089L27.2404 26.3093C27.4354 26.5267 27.5265 26.8042 27.5161 27.0774Z\" fill=\"#666666\"/> <path d=\"M30.889 23.8738C30.8786 24.1469 30.7668 24.4153 30.5561 24.6147C30.1343 25.0132 29.4762 24.9836 29.0862 24.5486L26.1261 21.2481C25.7361 20.8129 25.7617 20.1375 26.1833 19.7392C26.6051 19.3406 27.263 19.3702 27.6531 19.8053L30.6133 23.1057C30.8083 23.3231 30.8993 23.6008 30.889 23.8738Z\" fill=\"#666666\"/> <path d=\"M38.4676 83.6766C38.4572 83.9498 38.3454 84.2185 38.1343 84.4177C37.0069 85.4828 35.2407 85.4025 34.1969 84.239L33.0014 82.9061C32.6343 82.4965 32.6325 81.868 32.9971 81.4599L35.5249 78.6321C35.9125 78.1986 36.5707 78.1713 36.9948 78.5714C37.4191 78.9715 37.4487 79.6475 37.0611 80.0811L35.1787 82.1871L35.7244 82.7956C35.989 83.0907 36.4361 83.1114 36.7212 82.8422C37.1431 82.4435 37.8015 82.4734 38.1916 82.9083C38.3868 83.1258 38.4779 83.4036 38.4676 83.6766Z\" fill=\"#333333\"/> <path d=\"M82.535 35.8772L83.7296 37.2089C84.3848 37.9393 84.3418 39.0718 83.6353 39.7395L79.5827 38.2272L82.535 35.8772Z\" fill=\"#F9763D\"/> <path d=\"M85.2309 38.5454C85.2032 39.2764 84.9047 39.9951 84.3416 40.5268C83.9202 40.9252 83.2622 40.8956 82.8722 40.4608C82.4821 40.0261 82.5075 39.3505 82.9294 38.9524C83.2142 38.6829 83.2307 38.2242 82.9665 37.9296L82.4211 37.3215L80.222 39.0719C79.7693 39.4323 79.1158 39.3461 78.7626 38.8796C78.4095 38.4132 78.4899 37.7425 78.9428 37.382L81.8957 35.0316C82.3217 34.6924 82.9315 34.7463 83.2986 35.1554L84.4933 36.4873C85.015 37.0692 85.2586 37.8135 85.2309 38.5454Z\" fill=\"#333333\"/> <path d=\"M83.608 36.0372C83.5961 36.3511 83.4501 36.6436 83.2081 36.836L80.2548 39.1869C79.9132 39.4588 79.4421 39.4838 79.0724 39.25C79.0649 39.2452 78.8148 39.0873 78.3728 38.8263C78.2883 38.7757 78.2046 38.7264 78.1123 38.6739C78.1007 38.6674 78.0893 38.6605 78.0781 38.6536C78.0476 38.6347 78.015 38.6157 77.9815 38.5977C77.9692 38.5912 77.957 38.5842 77.945 38.5771C77.7959 38.4889 77.6333 38.3957 77.4571 38.2969C77.3536 38.2379 77.251 38.1803 77.1429 38.1224C77.1355 38.1185 77.1282 38.1143 77.1209 38.1103C76.8491 37.9566 76.5517 37.7936 76.2327 37.6234L76.0874 37.5466C76.0055 37.5031 75.9218 37.4587 75.8358 37.4145C73.6711 36.2776 71.6217 35.3631 69.7373 34.6924C69.5443 34.6241 69.348 34.5569 69.1504 34.4912C68.7877 34.3693 68.4532 34.2638 68.1247 34.1676C67.9713 34.1218 67.8238 34.0807 67.676 34.0397C67.4815 33.9865 67.2895 33.9366 67.1001 33.89L80.735 49.0925C81.087 49.4852 81.1005 50.0736 80.7897 50.4778C79.7649 51.9443 78.7043 53.3888 77.637 54.7724C76.1094 56.7556 74.4883 58.7171 72.819 60.6018C70.8767 62.7979 68.8273 64.9346 66.7283 66.9527C66.4743 67.199 66.2154 67.4469 65.955 67.6928C65.6947 67.9386 65.4329 68.183 65.1694 68.4255C63.0408 70.4022 60.7962 72.3226 58.5013 74.13C56.5506 75.6684 54.5116 77.1641 52.4416 78.575C51.0102 79.5555 49.5071 80.5298 47.9764 81.4693C47.5541 81.7284 47.011 81.6467 46.676 81.2732L33.0351 66.064C33.9154 71.9419 37.215 78.6849 37.254 78.7638C37.4499 79.161 37.3865 79.6404 37.0947 79.9672L34.5681 82.7939C34.3553 83.0323 34.0482 83.1578 33.7331 83.1355C33.4181 83.113 33.1294 82.9453 32.9481 82.6789C28.8488 76.6554 25.5675 69.9686 23.1951 62.8046C22.7471 61.451 22.3313 60.0789 21.9588 58.7264C21.9033 58.5264 21.8505 58.3278 21.7992 58.1312C21.2271 55.9982 20.7478 53.8653 20.3769 51.7986C20.2337 51.0051 19.0144 43.8976 20.3617 39.0797C20.5069 38.5601 21.0084 38.2362 21.5286 38.3258C26.7123 39.2182 31.8937 37.6434 35.7441 34.0052C39.5863 30.3751 41.5452 25.2159 41.1166 19.8537C41.0743 19.3103 41.434 18.8239 41.9541 18.7223C45.9711 17.9376 51.7783 19.0574 54.2877 19.7591C56.0573 20.2556 57.8371 20.8294 59.5786 21.4648C60.0309 21.6277 60.459 21.7876 60.8836 21.952C62.6923 22.6469 64.4842 23.4134 66.2069 24.2288C72.4095 27.15 78.1379 30.8315 83.2307 35.1701C83.4742 35.3775 83.6132 35.6866 83.6088 36.0107C83.6087 36.0193 83.6084 36.0282 83.608 36.0372ZM79.5328 37.0527L80.8967 35.9661C76.2016 32.1129 70.9763 28.8203 65.3454 26.1684C63.6675 25.3741 61.9238 24.6283 60.1604 23.9509C59.7483 23.7913 59.335 23.637 58.8942 23.4782C57.1977 22.8592 55.4681 22.3017 53.7494 21.8195C51.2505 21.1206 46.6056 20.3104 43.2449 20.6858C43.4205 26.3471 41.2324 31.7287 37.1566 35.58C33.0697 39.4417 27.6479 41.2333 22.1508 40.5718C21.4638 44.0832 21.9743 48.9389 22.4222 51.4197C22.7828 53.4269 23.2483 55.4993 23.8066 57.5801C23.8569 57.7735 23.907 57.9613 23.96 58.1524C24.3231 59.4712 24.728 60.8075 25.1644 62.1257C27.3293 68.6631 30.2701 74.7899 33.9147 80.3571L35.081 79.0532C34.0009 76.7281 30.6058 68.9299 30.7452 63.0661C30.7535 62.64 31.0216 62.248 31.4177 62.0963C31.8139 61.9446 32.2611 62.0554 32.5486 62.3759L47.6257 79.1866C48.8772 78.4049 50.1043 77.6025 51.2831 76.7949C53.3159 75.4094 55.3159 73.9423 57.2296 72.4333C59.481 70.66 61.6825 68.7768 63.7734 66.835C64.0336 66.5955 64.2888 66.3575 64.5425 66.1175C64.7965 65.8778 65.0487 65.6362 65.2992 65.3931C67.3611 63.4111 69.371 61.3153 71.2765 59.161C72.9146 57.3116 74.5047 55.3874 76.0033 53.4416C76.8894 52.2929 77.7706 51.1015 78.6298 49.8905L63.5581 33.0858C63.2704 32.765 63.2 32.2984 63.3803 31.9055C63.5603 31.5128 63.955 31.2726 64.378 31.2982C65.5271 31.3678 66.815 31.5959 68.2065 31.9766C68.3712 32.0222 68.5317 32.0669 68.6921 32.1149C69.0409 32.217 69.4008 32.3304 69.7861 32.4602C69.9932 32.5289 70.2016 32.6005 70.4083 32.6737C72.3858 33.3772 74.5254 34.3312 76.7695 35.5099C76.8559 35.5544 76.9463 35.6025 77.0349 35.6495L77.179 35.7256C77.516 35.9056 77.825 36.0747 78.1073 36.2345C78.2284 36.2993 78.3432 36.3637 78.4532 36.4264C78.6322 36.5268 78.8028 36.6247 78.9596 36.7172C79.0186 36.7494 79.076 36.7829 79.1306 36.8164C79.2306 36.8735 79.3221 36.9274 79.4088 36.9792C79.4518 37.0046 79.4931 37.0291 79.5328 37.0527Z\" fill=\"#333333\"/> <path d=\"M87.0187 69.2759C87.0081 69.5547 86.8913 69.8227 86.6856 70.0171L83.3111 73.2055C83.0759 73.4278 82.7532 73.5258 82.4369 73.4714C82.1205 73.4167 81.8457 73.2156 81.6916 72.9259C81.686 72.9156 81.1048 71.8283 80.0657 70.2568C79.4009 69.2479 78.6922 68.2569 77.9586 67.3095C77.1988 66.335 76.4196 65.4137 75.645 64.5741C74.8072 63.668 73.9501 62.8331 73.0985 62.0931C72.5184 61.5891 71.9337 61.1216 71.3606 60.7036L72.5601 58.9631C73.1814 59.4162 73.8135 59.9215 74.4385 60.4646C75.348 61.2548 76.2609 62.144 77.1516 63.1075C77.967 63.991 78.7846 64.9578 79.5829 65.9813C80.3522 66.9744 81.0929 68.0107 81.7866 69.0637C82.216 69.7128 82.5698 70.2813 82.8434 70.7363L84.8011 68.8864C84.5587 68.0752 84.2524 67.2381 83.8877 66.3894C83.4301 65.3216 82.8692 64.2104 82.2196 63.086C81.6325 62.0744 80.9706 61.0449 80.2534 60.0278C79.5674 59.0558 78.8302 58.0911 78.0627 57.1605C77.205 56.1168 76.4615 55.2996 75.9885 54.7976L77.4738 53.3082L77.4754 53.3097C77.9765 53.8415 78.755 54.697 79.6495 55.7856C80.4497 56.7559 81.2198 57.7638 81.9368 58.7797C82.6906 59.8487 83.3872 60.9324 84.007 62.0007C84.7006 63.2014 85.3005 64.3901 85.7912 65.5357C86.2914 66.6994 86.6927 67.8504 86.9833 68.9556C87.0114 69.0617 87.0227 69.1695 87.0187 69.2759Z\" fill=\"#333333\"/> <path d=\"M73.015 86.6723C73.0044 86.9526 72.8864 87.2199 72.682 87.4134L64.7311 94.9256C64.3864 95.2513 63.8708 95.2985 63.4727 95.0407C63.0747 94.7831 62.8928 94.2842 63.0288 93.8233L64.7117 88.1221L66.7033 88.7509L66.13 90.6931L70.1235 86.9197L68.6478 86.2178L69.5149 84.2799L72.4089 85.6564C72.7252 85.8068 72.9481 86.1091 73.0028 86.462C73.0137 86.5324 73.0177 86.6029 73.015 86.6723Z\" fill=\"#333333\"/> <path d=\"M92.6525 68.023C92.642 68.299 92.5275 68.5674 92.3196 68.7639L84.3724 76.2723C84.1172 76.5134 83.761 76.607 83.4228 76.5217C83.0848 76.4367 82.8098 76.1839 82.6899 75.8481L81.593 72.7757L83.5454 72.0493L84.1047 73.6159L88.0965 69.8447L86.1643 70.2705L85.7184 68.1824L91.3904 66.9325C91.8489 66.8316 92.3179 67.0587 92.5352 67.4869C92.6212 67.6568 92.6593 67.8414 92.6525 68.023Z\" fill=\"#333333\"/> <path d=\"M59.7554 76.0874L54.6719 80.8903L53.9882 80.1281L53.2333 79.3404C53.2413 79.3324 53.2508 79.323 53.259 79.3151L58.3425 74.5121L59.7554 76.0874Z\" fill=\"#333333\"/> <path d=\"M79.5797 57.2583L74.4946 62.0629L73.082 60.4877L78.1653 55.6847L79.5797 57.2583Z\" fill=\"#333333\"/> <path d=\"M62.0175 78.9851L57.3212 83.4222L55.9068 81.8486L60.6029 77.4115L62.0175 78.9851Z\" fill=\"#333333\"/> <path d=\"M79.5366 61.9147C79.5262 62.1878 79.4144 62.4562 79.2037 62.6556L77.114 64.6297C76.7038 65.0207 76.0601 65.0067 75.6637 64.5921C75.2601 64.1702 75.2637 63.4948 75.6728 63.0827C75.6808 63.0747 75.6906 63.0653 75.6986 63.0574L77.791 61.0805C78.2128 60.682 78.8709 60.7116 79.2609 61.1466C79.4557 61.364 79.547 61.6415 79.5366 61.9147Z\" fill=\"#333333\"/> <path d=\"M64.8659 80.8972C64.8556 81.1699 64.744 81.4379 64.5334 81.6368L62.1157 83.921C61.694 84.3195 61.0358 84.2899 60.6459 83.8549C60.2559 83.4197 60.2815 82.7442 60.7031 82.3459L63.1193 80.0632C63.5411 79.6647 64.1998 79.6937 64.59 80.1287C64.785 80.3463 64.8763 80.6243 64.8659 80.8972Z\" fill=\"#333333\"/> <path d=\"M83.8123 63.3308L79.472 67.4317C79.4638 67.4394 79.4554 67.447 79.447 67.4545L78.7412 66.6171L78.0592 65.8566L82.3994 61.7558L83.8123 63.3308Z\" fill=\"#333333\"/> <path d=\"M63.3559 87.7982L67.2629 84.0886L65.852 82.5078L61.945 86.2173L63.3559 87.7982Z\" fill=\"#333333\"/> <path d=\"M81.6154 70.4551L85.5226 66.7454L84.1117 65.1646L80.2044 68.8743L81.6154 70.4551Z\" fill=\"#333333\"/> <path d=\"M29.0675 58.9994C29.0572 59.2727 28.9453 59.5411 28.7345 59.7406L24.9248 63.3401L23.5115 61.7644L26.5572 58.8867L25.102 57.2642L23.5464 58.734L22.1332 57.1583L24.4525 54.9669C24.6552 54.7754 24.9238 54.675 25.1997 54.6874C25.4757 54.6999 25.7357 54.8242 25.9232 55.0331L28.7917 58.2312C28.9868 58.4485 29.0779 58.7261 29.0675 58.9994Z\" fill=\"#333333\"/> <path d=\"M66.7631 25.5311C66.5084 26.1406 66.1393 26.6759 65.6667 27.1225C63.8204 28.8662 60.9282 28.7354 59.2194 26.831C58.0412 25.5176 57.6881 23.6673 58.2981 22.0021L60.2444 22.7616C59.9125 23.6678 60.1044 24.6751 60.7455 25.3898C61.6758 26.4266 63.2502 26.498 64.255 25.549C64.5121 25.3063 64.7131 25.0144 64.852 24.6816L66.7631 25.5311Z\" fill=\"#333333\"/> <path d=\"M50.8983 45.6597C50.8931 45.7962 50.8372 45.9305 50.7318 46.0301C50.521 46.2295 50.192 46.2147 49.997 45.9971L46.7564 42.3839C46.5612 42.1665 46.574 41.8285 46.785 41.6295C46.9958 41.4302 47.3248 41.445 47.5198 41.6626L50.7604 45.2758C50.8579 45.3842 50.9035 45.5231 50.8983 45.6597Z\" fill=\"white\"/> <path d=\"M65.3707 32.3307C65.3603 32.6039 65.2485 32.8722 65.0377 33.0716L63.0241 34.9742C62.6023 35.3727 61.9442 35.3431 61.5542 34.9081C61.1643 34.4729 61.1899 33.7975 61.6114 33.3991L63.6251 31.4966C64.0468 31.0981 64.705 31.1277 65.0949 31.5627C65.2899 31.7801 65.381 32.0578 65.3707 32.3307Z\" fill=\"#333333\"/> <path d=\"M61.0955 36.3958C61.0851 36.6689 60.9733 36.9373 60.7625 37.1367L56.9274 40.7602C56.5057 41.1587 55.8476 41.1291 55.4576 40.6941C55.0676 40.2591 55.0932 39.5837 55.5148 39.1852L59.3499 35.5616C59.7717 35.1631 60.4298 35.1927 60.8197 35.6277C61.0147 35.8451 61.1058 36.1226 61.0955 36.3958Z\" fill=\"#333333\"/> <path d=\"M40.6179 55.855C40.6075 56.1281 40.4957 56.3965 40.285 56.5959L32.5058 63.946C32.084 64.3445 31.4259 64.3149 31.0359 63.8799C30.6459 63.4449 30.6716 62.7695 31.0931 62.371L38.8723 55.0208C39.2941 54.6223 39.9522 54.6519 40.3422 55.0869C40.5369 55.3043 40.6283 55.5818 40.6179 55.855Z\" fill=\"#333333\"/> <path d=\"M47.3877 35.4496L56.7925 45.9358L45.6091 56.5024L36.2043 46.0164L47.3877 35.4496Z\" fill=\"#158ACC\"/> <path d=\"M48.4657 40.4595L52.0173 44.4195C52.6896 45.169 52.6455 46.3316 51.9188 47.018L47.0629 51.6061C46.3362 52.2928 45.2037 52.2418 44.5316 51.4923L40.98 47.5323C40.3077 46.7828 40.3518 45.6202 41.0785 44.9337L45.9344 40.3457C46.6609 39.659 47.7934 39.7099 48.4657 40.4595Z\" fill=\"#DD582A\"/> <path d=\"M47.9763 41.8317L50.6446 44.8067C51.1496 45.3698 51.1165 46.2432 50.5705 46.7591L46.9223 50.2061C46.3763 50.722 45.5255 50.6837 45.0204 50.1206L42.3522 47.1456C41.8472 46.5825 41.8803 45.709 42.4262 45.1932L46.0745 41.7462C46.6204 41.2303 47.4713 41.2686 47.9763 41.8317Z\" fill=\"#F73E3E\"/> <path d=\"M57.8321 45.9826C57.8218 46.2557 57.71 46.5241 57.4992 46.7235L46.3158 57.2901C45.894 57.6886 45.2359 57.659 44.8459 57.224L39.7833 51.5793C39.3933 51.1443 39.419 50.4689 39.8405 50.0704C40.2623 49.6719 40.9204 49.7015 41.3104 50.1365L45.6668 54.9937L55.3231 45.87L47.3309 36.959L37.6746 46.0827L38.948 47.5025C39.3379 47.9375 39.3123 48.6129 38.8908 49.0115C38.469 49.41 37.8109 49.3804 37.4209 48.9454L35.4413 46.7382C35.0513 46.3031 35.077 45.6277 35.4985 45.2292L46.6819 34.6626C47.1037 34.2641 47.7618 34.2937 48.1518 34.7287L57.5568 45.215C57.7512 45.4317 57.8425 45.7094 57.8321 45.9826Z\" fill=\"#333333\"/> <path d=\"M52.3962 45.8334C52.3714 46.4881 52.1037 47.1319 51.5995 47.6085L47.6624 51.3284C47.1735 51.7904 46.5381 52.0283 45.873 51.9984C45.2078 51.9685 44.5926 51.6743 44.1403 51.17L41.2607 47.9595C40.3275 46.9189 40.389 45.297 41.3978 44.3437L45.3348 40.6238C46.3435 39.6707 47.9238 39.7418 48.8569 40.7822L51.7366 43.9929C52.203 44.513 52.421 45.1784 52.3962 45.8334ZM42.6785 46.2123C42.6744 46.3205 42.7104 46.4307 42.7877 46.5167L45.6673 49.7274C45.7684 49.8401 45.8903 49.8618 45.9539 49.8647C46.0175 49.8675 46.1405 49.8568 46.2498 49.7536L50.1868 46.0335C50.3535 45.876 50.3637 45.6077 50.2095 45.4355L47.3299 42.2249C47.1756 42.0529 46.9143 42.0412 46.7474 42.1987L42.8104 45.9185C42.7268 45.9975 42.6826 46.1039 42.6785 46.2123Z\" fill=\"#333333\"/> <path d=\"M31.8102 45.4914C31.8093 45.5149 31.8078 45.5386 31.8052 45.5623C31.745 46.1443 31.2341 46.5642 30.6638 46.5001L20.7469 45.3841C20.1766 45.3199 19.7625 44.7973 19.823 44.2138C19.883 43.6317 20.3942 43.2119 20.9644 43.276L30.8813 44.392C31.4284 44.4534 31.8313 44.9381 31.8102 45.4914Z\" fill=\"#333333\"/> <path d=\"M37.2647 46.0911C37.2638 46.1147 37.2622 46.1386 37.2597 46.1624C37.1994 46.7477 36.688 47.17 36.1172 47.1055L34.6809 46.9432C34.1102 46.8787 33.696 46.3516 33.7563 45.7663C33.8166 45.1809 34.328 44.7586 34.8987 44.8231L36.335 44.9855C36.8825 45.0472 37.2858 45.5347 37.2647 46.0911Z\" fill=\"#333333\"/> <path d=\"M48.4515 80.6781C48.4312 81.2125 48.0224 81.6566 47.488 81.6971C46.9117 81.7409 46.4074 81.2986 46.3619 80.7093L45.1741 65.3611C45.1285 64.7736 45.5587 64.2587 46.1349 64.2148C46.7112 64.171 47.2155 64.6134 47.261 65.2027L48.4488 80.5508C48.4522 80.5936 48.4531 80.6362 48.4515 80.6781Z\" fill=\"#333333\"/> <path d=\"M46.965 60.991C46.9447 61.525 46.5373 61.9689 46.0047 62.0095C45.4305 62.0533 44.9279 61.6111 44.8826 61.0221L44.5422 56.611C44.4975 56.0226 44.9255 55.509 45.4997 55.4652C46.074 55.4214 46.5766 55.8636 46.6219 56.4526L46.9623 60.8637C46.9657 60.9067 46.9666 60.9491 46.965 60.991Z\" fill=\"#333333\"/> <path d=\"M48.4653 35.4675C48.444 36.0258 48.0023 36.4767 47.4482 36.4894C46.8706 36.5025 46.3895 36.0342 46.3738 35.4435L46.1257 26.1142C46.1105 25.5227 46.5656 25.0338 47.1432 25.0207C47.7208 25.0075 48.2019 25.4758 48.2175 26.0666L48.4657 35.3958C48.4662 35.42 48.4662 35.4438 48.4653 35.4675Z\" fill=\"#333333\"/> <path d=\"M48.1434 22.6258C48.1222 23.1837 47.682 23.6344 47.1299 23.6471C46.5543 23.6602 46.0749 23.1922 46.0593 22.6018L45.9783 19.5494C45.9642 18.9588 46.4167 18.4695 46.9923 18.4564C47.5678 18.4433 48.0473 18.9113 48.0629 19.5017L48.1438 22.5541C48.1444 22.5781 48.1443 22.6021 48.1434 22.6258Z\" fill=\"#333333\"/> <path d=\"M80.9539 49.787C80.9523 49.8287 80.9482 49.8708 80.9419 49.9128C80.8522 50.4921 80.3204 50.8852 79.7539 50.7907L72.2112 49.5331C71.6447 49.4386 71.2581 48.8925 71.3475 48.3132C71.4371 47.734 71.969 47.3409 72.5355 47.4354L80.0782 48.6929C80.6034 48.7805 80.9741 49.2566 80.9539 49.787Z\" fill=\"#333333\"/> <path d=\"M69.6676 47.9211C69.666 47.9627 69.6619 48.0048 69.6555 48.0468C69.5659 48.6251 69.0342 49.0176 68.4677 48.9233L56.6043 46.9481C56.0379 46.8538 55.6514 46.3093 55.7408 45.73C55.8304 45.1517 56.3622 44.7592 56.9286 44.8535L68.792 46.8287C69.3171 46.9163 69.6877 47.3915 69.6676 47.9211Z\" fill=\"#333333\"/> <path d=\"M68.2351 9.46831C68.2128 10.0547 67.73 10.5095 67.1569 10.4838L62.7079 10.2844C62.1348 10.2587 61.6882 9.76231 61.7105 9.17589C61.7328 8.58946 62.2156 8.13474 62.7887 8.16042L67.2375 8.3598C67.8108 8.3855 68.2574 8.88188 68.2351 9.46831Z\" fill=\"#FCBC1D\"/> <path d=\"M66.1036 7.07825L65.9295 11.66C65.9071 12.2501 65.4215 12.7078 64.8452 12.6819C64.2688 12.6561 63.8196 12.1565 63.8421 11.5663L64.0162 6.98463C64.0386 6.39444 64.5242 5.93679 65.1005 5.96264C65.6769 5.98849 66.1261 6.48784 66.1036 7.07825Z\" fill=\"#FCBC1D\"/> <path d=\"M8.59589 66.0799C8.57358 66.6664 8.09075 67.1211 7.51766 67.0954L3.0689 66.896C2.49581 66.8703 2.04916 66.374 2.07146 65.7875C2.09377 65.2011 2.5766 64.7464 3.14969 64.7721L7.59845 64.9714C8.17175 64.9971 8.61819 65.4935 8.59589 66.0799Z\" fill=\"#FCBC1D\"/> <path d=\"M6.46458 63.6899L6.29044 68.2716C6.26801 68.8618 5.78245 69.3194 5.20612 69.2936C4.62979 69.2677 4.1806 68.7682 4.20304 68.178L4.37717 63.5963C4.3996 63.0061 4.88516 62.5484 5.46149 62.5743C6.03783 62.6001 6.48702 63.0995 6.46458 63.6899Z\" fill=\"#FCBC1D\"/> </svg>",
					"right": "<svg width=\"119\" height=\"124\" viewBox=\"0 0 119 124\" fill=\"none\" xmlns=\"http://www.w3.org/2000/svg\"> <path d=\"M117.719 74.7005L108.587 65.2813L97.1101 77.1182L106.243 86.5375L117.719 74.7005Z\" fill=\"#FCBC1D\"/> <path d=\"M99.4561 55.8633L108.587 65.2809L97.11 77.1183L87.9792 67.7004L89.4651 66.1679L99.4561 55.8633Z\" fill=\"#FCBC1D\"/> <path d=\"M56.3205 11.3728L65.4512 20.7904L55.4605 31.0952L53.9746 32.6277L44.8436 23.2102L56.3205 11.3728Z\" fill=\"#FCBC1D\"/> <path d=\"M56.3206 11.3731L47.1898 1.95554L35.7134 13.7925L44.8442 23.2101L56.3206 11.3731Z\" fill=\"#FCBC1D\"/> <path d=\"M71.4138 38.901C73.9187 39.4073 76.3091 40.6629 78.2499 42.6647C80.1908 44.6664 81.4081 47.1319 81.8972 49.7137C78.968 51.3273 75.2439 50.8618 72.7731 48.3133C70.3022 45.7648 69.8491 41.9219 71.4138 38.901Z\" fill=\"#FCBC1D\"/> <path d=\"M106.243 86.5375L97.1101 77.1183L85.6319 88.957L94.7643 98.3763L106.243 86.5375Z\" fill=\"#FCBC1D\"/> <path d=\"M87.9791 67.7004L97.1099 77.1183L85.6315 88.9572L76.5005 79.5396L84.1249 71.6757L87.9791 67.7004Z\" fill=\"#FCBC1D\"/> <path d=\"M44.8437 23.2101L53.9747 32.6277L50.1205 36.603L42.4961 44.4669L33.3654 35.0491L44.8437 23.2101Z\" fill=\"#FCBC1D\"/> <path d=\"M44.8438 23.2103L35.713 13.7927L24.2348 25.6315L33.3656 35.0491L44.8438 23.2103Z\" fill=\"#FCBC1D\"/> <path d=\"M78.2482 62.0869L59.4172 42.6644C62.6779 39.3013 67.2074 38.0473 71.4139 38.9007C69.8494 41.9219 70.3026 45.7646 72.7732 48.313C75.2438 50.8615 78.9681 51.3271 81.8972 49.7134C82.0648 50.5917 82.1486 51.4824 82.1486 52.3747C82.1501 55.8897 80.849 59.4045 78.2482 62.0869Z\" fill=\"#23464F\"/> <path d=\"M59.4171 42.6644L78.2481 62.0869L76.1226 64.2792L70.7828 69.7868L64.9621 75.7903L60.1403 80.7635L41.3093 61.341L46.1311 56.3677L51.9518 50.3642L57.2916 44.8567L59.4171 42.6644Z\" fill=\"#F9911E\"/> <path opacity=\"0.25\" d=\"M59.4172 42.6644L78.2482 62.0869L76.1229 64.2789L70.7829 69.7868L64.9625 75.79C64.9625 75.79 73.8796 69.0665 60.1407 80.7633C69.2015 59.6965 59.4172 42.6644 59.4172 42.6644Z\" fill=\"black\"/> <path d=\"M94.7637 98.3766L85.6313 88.9573L74.1549 100.794L83.2873 110.213L94.7637 98.3766Z\" fill=\"#FCBC1D\"/> <path d=\"M76.5005 79.5397L85.6315 88.9572L74.1547 100.795L65.0239 91.377L66.7936 89.5515L76.5005 79.5397Z\" fill=\"#FCBC1D\"/> <path d=\"M33.3654 35.0491L42.4961 44.4669L32.7892 54.4788L31.0196 56.304L21.8885 46.8865L33.3654 35.0491Z\" fill=\"#FCBC1D\"/> <path d=\"M33.3653 35.0494L24.2345 25.6318L12.7581 37.4688L21.8889 46.8864L33.3653 35.0494Z\" fill=\"#FCBC1D\"/> <path d=\"M41.3094 61.341L60.1404 80.7635L56.3205 84.7034L53.0614 81.3419L40.7504 68.644L37.4895 65.2809L41.3094 61.341Z\" fill=\"#23464F\"/> <path d=\"M83.2871 110.214L74.1547 100.795L62.6783 112.632L71.8107 122.051L83.2871 110.214Z\" fill=\"#FCBC1D\"/> <path d=\"M74.1544 100.795L65.0237 91.3773L53.5473 103.214L62.678 112.632L74.1544 100.795Z\" fill=\"#FCBC1D\"/> <path d=\"M31.0194 56.3043L21.8887 46.8867L10.4123 58.7236L19.543 68.1412L31.0194 56.3043Z\" fill=\"#FCBC1D\"/> <path d=\"M21.8886 46.8867L12.7578 37.4691L1.28141 49.306L10.4122 58.7236L21.8886 46.8867Z\" fill=\"#FCBC1D\"/> <path d=\"M56.3203 11.3728L65.4511 20.7904L55.4603 31.0952L53.9745 32.6277L56.3203 11.3728Z\" fill=\"#FCD277\"/> <path d=\"M47.1897 1.95523L56.3205 11.3728L44.8436 23.2102L47.1897 1.95523Z\" fill=\"#FCD277\"/> <path d=\"M44.8436 23.2102L53.9746 32.6277L50.1204 36.603L42.496 44.467L44.8436 23.2102Z\" fill=\"#FCD277\"/> <path d=\"M35.7129 13.7926L44.8436 23.2102L33.3652 35.0491L35.7129 13.7926Z\" fill=\"#FCD277\"/> <path d=\"M33.3654 35.0491L42.4961 44.467L32.7892 54.4788L31.0195 56.3041L33.3654 35.0491Z\" fill=\"#FCD277\"/> <path d=\"M21.8885 46.8865L33.3654 35.0491L24.2346 25.6316L21.8885 46.8865Z\" fill=\"#FCD277\"/> <path d=\"M21.8884 46.8865L31.0194 56.3041L19.5426 68.1414L21.8884 46.8865Z\" fill=\"#FCD277\"/> <path d=\"M12.7576 37.4689L21.8883 46.8865L10.4117 58.7238L12.7576 37.4689Z\" fill=\"#FCD277\"/> <path d=\"M53.062 81.3419L52.6805 81.7383L50.7256 83.7517L48.1999 81.1464L39.1389 90.4921L41.6648 93.0974L38.9288 95.9193L38.8235 95.811L26.6168 83.2232L29.3526 80.4013L31.8787 83.0039L40.9396 73.6582L38.5187 71.1613L38.4139 71.0529L38.4702 70.9948L40.3683 69.0395L40.75 68.6432L53.062 81.3419Z\" fill=\"#FCBC1D\"/> <path d=\"M50.7258 83.7512L54.0139 87.1425L44.9516 96.4895L41.6635 93.0982L39.1378 90.4934L48.2004 81.1461L50.7258 83.7512Z\" fill=\"#23464F\"/> <path d=\"M38.4146 71.0532L40.94 73.658L31.8777 83.005L29.3523 80.4002L26.0642 77.0089L35.1266 67.6619L38.4146 71.0532Z\" fill=\"#23464F\"/> <path d=\"M56.3208 86.0246C55.9931 86.0246 55.6652 85.8956 55.4152 85.6377L52.1558 82.2762C51.6555 81.7602 51.6555 80.9239 52.1555 80.4079C52.6559 79.8919 53.4667 79.8919 53.967 80.4079L56.3208 82.8353L77.3428 61.1529C79.6175 58.8068 80.8694 55.6895 80.8679 52.3755C80.8679 51.5686 80.7913 50.7593 80.6404 49.969C80.4083 48.7424 79.9989 47.5658 79.4238 46.4701C79.0872 45.8283 79.3185 45.0266 79.9408 44.6794C80.5628 44.3317 81.3403 44.5705 81.6769 45.2123C82.3758 46.544 82.8727 47.9732 83.1545 49.4608C83.3369 50.4171 83.4297 51.3984 83.4297 52.3753C83.4315 56.395 81.9131 60.176 79.1543 63.0215L57.2266 85.638C56.9763 85.8954 56.6484 86.0246 56.3208 86.0246Z\" fill=\"#333333\"/> <path d=\"M78.2497 43.9855C77.9218 43.9855 77.5939 43.8566 77.3438 43.5984C76.9009 43.1413 76.4216 42.7178 75.9195 42.3394C75.3482 41.909 75.2234 41.0825 75.6407 40.4932C76.0578 39.9043 76.8596 39.7753 77.4304 40.206C78.0388 40.6645 78.6193 41.1773 79.1553 41.7304C79.6553 42.2464 79.6553 43.0829 79.155 43.5987C78.9052 43.8566 78.5776 43.9855 78.2497 43.9855Z\" fill=\"#333333\"/> <path d=\"M40.7501 69.9651C40.4224 69.9651 40.0943 69.8362 39.8445 69.5783L36.5839 66.2152C36.0835 65.6992 36.0835 64.8626 36.5839 64.3468L58.5115 41.7303C61.9579 38.1754 66.8748 36.6329 71.661 37.6047C72.376 37.7492 73.0858 37.9508 73.7696 38.2037C74.4356 38.45 74.7817 39.2062 74.5432 39.8932C74.3042 40.5801 73.5708 40.9377 72.905 40.6909C72.3419 40.4827 71.7573 40.3165 71.1673 40.1973C67.2178 39.3954 63.1645 40.6676 60.3227 43.5987L39.3009 65.2809L41.6557 67.7099C42.156 68.226 42.156 69.0625 41.6557 69.5783C41.4059 69.8362 41.078 69.9651 40.7501 69.9651Z\" fill=\"#333333\"/> <path d=\"M78.2482 63.1438C77.9862 63.1438 77.7238 63.0405 77.5238 62.8344L58.6925 43.4119C58.2921 42.9992 58.2921 42.3299 58.6925 41.9171C59.0924 41.5044 59.7413 41.5044 60.1415 41.9171L78.9727 61.3397C79.3731 61.7524 79.3731 62.4217 78.9727 62.8344C78.7729 63.0405 78.5106 63.1438 78.2482 63.1438Z\" fill=\"#333333\"/> <path d=\"M46.1327 57.6889C46.0746 57.6889 46.0162 57.6849 45.957 57.6764L32.6149 55.7878C31.914 55.6887 31.4239 55.022 31.5203 54.2994C31.6166 53.5764 32.2629 53.071 32.9633 53.1701L46.3054 55.0588C47.0063 55.1578 47.4964 55.8245 47.4001 56.5471C47.3122 57.2093 46.7629 57.6889 46.1327 57.6889Z\" fill=\"#333333\"/> <path d=\"M39.8099 91.1844L41.6646 93.0974L38.9286 95.9193L38.8236 95.811C39.2463 94.2336 39.5691 92.6878 39.8099 91.1844Z\" fill=\"#D37A22\"/> <path opacity=\"0.25\" d=\"M52.6805 81.7383L50.7258 83.7517L48.1999 81.1464L40.0355 89.5673C40.7118 84.0608 40.2891 79.1462 39.4975 75.1458C39.208 73.6899 38.8724 72.3556 38.5189 71.1613C38.5035 71.1058 38.4856 71.0503 38.4702 70.9948L40.3685 69.0395L52.6805 81.7383Z\" fill=\"black\"/> <path d=\"M57.2904 46.1778C56.6602 46.1778 56.1109 45.6982 56.0231 45.0361L54.1919 31.2746C54.0956 30.552 54.5856 29.8853 55.2865 29.7862C55.9892 29.6856 56.6335 30.1929 56.7296 30.9155L58.5608 44.677C58.6571 45.3997 58.167 46.0663 57.4661 46.1654C57.4069 46.1738 57.348 46.1778 57.2904 46.1778Z\" fill=\"#333333\"/> <path d=\"M51.9504 51.6856C51.3202 51.6856 50.771 51.2061 50.6831 50.5439L48.8519 36.7824C48.7556 36.0598 49.2457 35.3931 49.9466 35.294C50.6493 35.1936 51.2936 35.7007 51.3896 36.4234L53.2208 50.1848C53.3171 50.9075 52.8271 51.5741 52.1262 51.6732C52.067 51.6817 52.0083 51.6856 51.9504 51.6856Z\" fill=\"#333333\"/> <path d=\"M66.7922 90.8729C66.162 90.8729 65.6128 90.3933 65.5249 89.7311L63.6937 75.9697C63.5974 75.247 64.0875 74.5804 64.7884 74.4813C65.4919 74.3809 66.1351 74.8879 66.2315 75.6106L68.0626 89.3721C68.159 90.0947 67.6689 90.7614 66.968 90.8605C66.9088 90.8689 66.8499 90.8729 66.7922 90.8729Z\" fill=\"#333333\"/> <path d=\"M89.4666 67.4893C89.4085 67.4893 89.35 67.4854 89.2909 67.4769L75.9485 65.5882C75.2476 65.4891 74.7576 64.8225 74.8539 64.0998C74.9499 63.3769 75.5978 62.8712 76.2969 62.9705L89.6393 64.8592C90.3402 64.9583 90.8302 65.625 90.7339 66.3476C90.6461 67.0095 90.0968 67.4893 89.4666 67.4893Z\" fill=\"#333333\"/> <path d=\"M84.1268 72.9971C84.0686 72.9971 84.0102 72.9932 83.951 72.9847L70.6087 71.096C69.9078 70.9969 69.4177 70.3303 69.514 69.6076C69.6104 68.8847 70.2567 68.3787 70.9571 68.4783L84.2994 70.367C85.0003 70.4661 85.4904 71.1328 85.3941 71.8554C85.306 72.5173 84.757 72.9971 84.1268 72.9971Z\" fill=\"#333333\"/> <path d=\"M108.586 65.2809L117.717 74.6985L107.726 85.0033L106.24 86.5358L108.586 65.2809Z\" fill=\"#FCD277\"/> <path d=\"M99.456 55.8633L108.587 65.2809L97.1099 77.1183L99.456 55.8633Z\" fill=\"#FCD277\"/> <path d=\"M97.1097 77.1183L106.24 86.5358L102.386 90.5109L94.7621 98.3748L97.1097 77.1183Z\" fill=\"#FCD277\"/> <path d=\"M87.979 67.7004L97.1097 77.1183L85.6313 88.9572L87.979 67.7004Z\" fill=\"#FCD277\"/> <path d=\"M85.6315 88.9572L94.7622 98.3748L85.0551 108.387L83.2854 110.212L85.6315 88.9572Z\" fill=\"#FCD277\"/> <path d=\"M74.1545 100.795L85.6314 88.9572L76.5004 79.5397L74.1545 100.795Z\" fill=\"#FCD277\"/> <path d=\"M74.1546 100.795L83.2853 110.212L71.8085 122.05L74.1546 100.795Z\" fill=\"#FCD277\"/> <path d=\"M65.0237 91.377L74.1544 100.795L62.6776 112.632L65.0237 91.377Z\" fill=\"#FCD277\"/> <path d=\"M19.5426 69.4625C19.215 69.4625 18.8868 69.3336 18.6371 69.0757L9.50605 59.6581L0.375303 50.2403C0.13475 49.9924 0 49.6566 0 49.306C0 48.9553 0.13475 48.6195 0.375303 48.3717L46.2842 1.02086C46.784 0.50509 47.5956 0.50509 48.0954 1.02086L66.3569 19.8563C66.8572 20.3723 66.8572 21.2089 66.3569 21.7246L20.4482 69.0757C20.1985 69.3336 19.8703 69.4625 19.5426 69.4625ZM11.3175 57.7895L19.5426 66.2728L63.6398 20.7906L47.1898 3.82378L3.09234 49.306L11.3175 57.7895Z\" fill=\"#333333\"/> <path d=\"M52.8723 16.2504C52.5446 16.2504 52.2165 16.1215 51.9664 15.8636C51.4664 15.3476 51.4664 14.511 51.9667 13.9953L55.4151 10.4388C55.9149 9.923 56.7263 9.923 57.2266 10.4388C57.7266 10.9548 57.7266 11.7913 57.2263 12.3071L53.7779 15.8636C53.5279 16.1215 53.1999 16.2504 52.8723 16.2504Z\" fill=\"#333333\"/> <path d=\"M10.4118 60.045C10.0842 60.045 9.756 59.916 9.50622 59.6582C9.0059 59.1421 9.0059 58.3056 9.50622 57.7898L49.0631 16.99C49.5629 16.4742 50.3745 16.4742 50.8743 16.99C51.3746 17.506 51.3746 18.3426 50.8743 18.8584L11.3174 59.6582C11.0674 59.916 10.7395 60.045 10.4118 60.045Z\" fill=\"#333333\"/> <path d=\"M53.9745 33.9489C53.6468 33.9489 53.3186 33.8199 53.0689 33.562L34.8074 14.7266C34.307 14.2106 34.307 13.374 34.8074 12.8583C35.3072 12.3425 36.1187 12.3425 36.6186 12.8583L54.8801 31.6937C55.3804 32.2097 55.3804 33.0463 54.8801 33.562C54.6303 33.8199 54.3024 33.9489 53.9745 33.9489Z\" fill=\"#333333\"/> <path d=\"M42.496 45.7881C42.1683 45.7881 41.8402 45.6591 41.5904 45.4013L37.7859 41.4772C37.2856 40.9612 37.2856 40.1246 37.7859 39.6089C38.2857 39.0931 39.0973 39.0931 39.5971 39.6089L43.4016 43.5329C43.9019 44.0489 43.9019 44.8855 43.4016 45.4013C43.1516 45.6589 42.8237 45.7881 42.496 45.7881Z\" fill=\"#333333\"/> <path d=\"M36.1298 39.2218C35.8021 39.2218 35.4739 39.0928 35.2242 38.8349L23.3287 26.5658C22.8284 26.0498 22.8284 25.2132 23.3287 24.6975C23.8285 24.1817 24.6401 24.1817 25.1399 24.6975L37.0354 36.9666C37.5357 37.4826 37.5357 38.3192 37.0354 38.8349C36.7856 39.0928 36.4577 39.2218 36.1298 39.2218Z\" fill=\"#333333\"/> <path d=\"M31.0194 57.6252C30.6918 57.6252 30.3636 57.4962 30.1138 57.2384L16.9165 43.6265C16.4162 43.1104 16.4162 42.2739 16.9165 41.7581C17.4163 41.2423 18.2279 41.2423 18.7277 41.7581L31.925 55.37C32.4254 55.886 32.4254 56.7226 31.925 57.2384C31.6753 57.4962 31.3471 57.6252 31.0194 57.6252Z\" fill=\"#333333\"/> <path d=\"M15.3453 41.4593C15.0177 41.4593 14.6895 41.3303 14.4397 41.0724L11.8518 38.4032C11.3515 37.8872 11.3515 37.0506 11.8518 36.5349C12.3516 36.0191 13.1632 36.0191 13.663 36.5349L16.2509 39.2041C16.7512 39.7201 16.7512 40.5567 16.2509 41.0724C16.0011 41.3301 15.6732 41.4593 15.3453 41.4593Z\" fill=\"#333333\"/> <path d=\"M71.8104 123.372C71.4827 123.372 71.1545 123.243 70.9048 122.985L52.6415 104.148C52.1412 103.632 52.1412 102.796 52.6415 102.28L98.5501 54.929C99.0499 54.4132 99.8615 54.4132 100.361 54.929L118.625 73.766C119.125 74.282 119.125 75.1186 118.625 75.6344L72.7162 122.985C72.4662 123.243 72.1383 123.372 71.8104 123.372ZM63.5834 111.698L71.8104 120.183L115.908 74.7003L99.4557 57.7317L55.3588 103.214L63.5834 111.698Z\" fill=\"#333333\"/> <path d=\"M92.5001 83.1939C92.1724 83.1939 91.8443 83.0649 91.5945 82.8071C91.0942 82.291 91.0942 81.4545 91.5945 80.9387L107.681 64.3468C108.181 63.8311 108.993 63.8311 109.492 64.3468C109.993 64.8629 109.993 65.6994 109.492 66.2152L93.4057 82.8071C93.1559 83.0649 92.8277 83.1939 92.5001 83.1939Z\" fill=\"#333333\"/> <path d=\"M62.6778 113.953C62.3502 113.953 62.022 113.824 61.7722 113.566C61.2719 113.05 61.2719 112.214 61.7722 111.698L87.6666 84.9901C88.1664 84.4744 88.978 84.4744 89.4778 84.9901C89.9781 85.5062 89.9781 86.3427 89.4778 86.8585L63.5834 113.566C63.3336 113.824 63.0055 113.953 62.6778 113.953Z\" fill=\"#333333\"/> <path d=\"M106.242 87.8588C105.915 87.8588 105.587 87.7299 105.337 87.472L100.417 82.3978C99.9172 81.8818 99.9172 81.0452 100.417 80.5294C100.917 80.0137 101.729 80.0137 102.229 80.5294L107.148 85.6036C107.648 86.1197 107.648 86.9562 107.148 87.472C106.898 87.7296 106.57 87.8588 106.242 87.8588Z\" fill=\"#333333\"/> <path d=\"M99.1863 80.581C98.8586 80.581 98.5305 80.452 98.2804 80.1941L87.0736 68.635C86.5733 68.119 86.5733 67.2824 87.0736 66.7667C87.5734 66.2509 88.385 66.2509 88.8848 66.7667L100.092 78.3258C100.592 78.8418 100.592 79.6784 100.092 80.1941C99.8418 80.4518 99.5139 80.581 99.1863 80.581Z\" fill=\"#333333\"/> <path d=\"M94.7639 99.6978C94.4362 99.6978 94.108 99.5688 93.8583 99.3109L75.595 80.4739C75.0946 79.9579 75.0946 79.1213 75.595 78.6056C76.0948 78.0898 76.9064 78.0898 77.4062 78.6056L95.6694 97.4426C96.1698 97.9586 96.1698 98.7952 95.6694 99.3109C95.4197 99.5688 95.0915 99.6978 94.7639 99.6978Z\" fill=\"#333333\"/> <path d=\"M83.2873 111.535C82.9596 111.535 82.6315 111.406 82.3817 111.148L70.1163 98.4976C69.616 97.9816 69.616 97.1451 70.1163 96.6293C70.6161 96.1135 71.4277 96.1135 71.9275 96.6293L84.1929 109.28C84.6932 109.796 84.6932 110.632 84.1929 111.148C83.9431 111.406 83.6152 111.535 83.2873 111.535Z\" fill=\"#333333\"/> <path d=\"M68.3736 96.1529C68.0459 96.1529 67.7177 96.024 67.468 95.7661L64.1182 92.3111C63.6178 91.7951 63.6178 90.9585 64.1182 90.4427C64.618 89.927 65.4295 89.927 65.9293 90.4427L69.2792 93.8978C69.7795 94.4138 69.7795 95.2503 69.2792 95.7661C69.0294 96.024 68.7015 96.1529 68.3736 96.1529Z\" fill=\"#333333\"/> <path d=\"M78.2366 51.9873C75.9067 51.9873 73.6131 51.0477 71.8675 49.2473C69.0352 46.3263 68.3988 41.9182 70.2838 38.2782C70.6171 37.6345 71.3933 37.3914 72.0171 37.7355C72.6411 38.0792 72.8766 38.8796 72.5435 39.5232C71.2147 42.0886 71.6818 45.319 73.6789 47.3787C75.7066 49.4703 78.7669 49.9398 81.2939 48.5479C81.9179 48.2039 82.6939 48.4472 83.0272 49.0906C83.3605 49.7343 83.1248 50.5346 82.5007 50.8784C81.1478 51.624 79.6851 51.9873 78.2366 51.9873Z\" fill=\"#333333\"/> <path d=\"M60.1403 82.0847C59.8127 82.0847 59.4845 81.9557 59.2347 81.6978L53.1794 75.452C52.6791 74.936 52.6791 74.0995 53.1794 73.5837C53.6792 73.0679 54.4908 73.0679 54.9906 73.5837L61.0459 79.8295C61.5463 80.3455 61.5463 81.1821 61.0459 81.6978C60.7959 81.9557 60.468 82.0847 60.1403 82.0847Z\" fill=\"#333333\"/> <path d=\"M51.3521 73.0204C51.0245 73.0204 50.6963 72.8914 50.4466 72.6336L40.4038 62.2753C39.9035 61.7593 39.9035 60.9227 40.4038 60.407C40.9036 59.8912 41.7152 59.8912 42.215 60.407L52.2577 70.7652C52.7581 71.2812 52.7581 72.1178 52.2577 72.6336C52.008 72.8914 51.6798 73.0204 51.3521 73.0204Z\" fill=\"#333333\"/> <path d=\"M38.9276 97.241C38.5879 97.241 38.262 97.1017 38.022 96.8542L25.7108 84.1562C25.4705 83.9084 25.3354 83.5725 25.3354 83.2219C25.3354 82.8713 25.4702 82.5355 25.7108 82.2876L28.4467 79.4659C28.9466 78.9502 29.7581 78.9502 30.2579 79.4659C30.7583 79.982 30.7583 80.8185 30.2579 81.3343L28.4278 83.2219L38.9273 94.0515L40.7577 92.1639C41.2575 91.6481 42.0691 91.6481 42.5689 92.1639C43.0692 92.6799 43.0692 93.5165 42.5689 94.0322L39.8329 96.8542C39.5931 97.102 39.2673 97.241 38.9276 97.241Z\" fill=\"#333333\"/> <path d=\"M50.7258 85.0723C50.3982 85.0723 50.07 84.9434 49.8202 84.6855C49.3199 84.1694 49.3199 83.3332 49.8202 82.8171L51.25 81.3422L40.7505 70.5129L39.3205 71.9878C38.8207 72.5036 38.0091 72.5036 37.5093 71.9878C37.009 71.4717 37.009 70.6352 37.5093 70.1194L39.8449 67.7105C40.3447 67.1947 41.1562 67.1947 41.656 67.7105L53.9673 80.4084C54.4676 80.9245 54.4676 81.761 53.9673 82.2768L51.6317 84.686C51.3814 84.9431 51.0535 85.0723 50.7258 85.0723Z\" fill=\"#333333\"/> <path d=\"M31.878 84.3264C31.5383 84.3264 31.2124 84.1871 30.9724 83.9395L25.1586 77.9432C24.9183 77.6953 24.7833 77.3595 24.7833 77.0089C24.7833 76.6582 24.9181 76.3224 25.1586 76.0746L34.2212 66.7275C34.721 66.2118 35.5326 66.2118 36.0324 66.7275L41.8459 72.7236C42.3462 73.2397 42.3462 74.0762 41.8459 74.592L32.7836 83.939C32.5433 84.1871 32.2177 84.3264 31.878 84.3264ZM27.8757 77.0089L31.878 81.1369L39.1289 73.6582L35.1268 69.5302L27.8757 77.0089Z\" fill=\"#333333\"/> <path d=\"M44.9515 97.8107C44.6118 97.8107 44.2859 97.6714 44.0459 97.4239L38.2324 91.4275C37.7321 90.9115 37.7321 90.0749 38.2324 89.5592L47.2948 80.2121C47.7946 79.6963 48.6061 79.6963 49.106 80.2121L54.9194 86.2082C55.4198 86.7243 55.4198 87.5608 54.9194 88.0766L45.8571 97.4236C45.6168 97.6715 45.2912 97.8107 44.9515 97.8107ZM40.9495 90.4932L44.9515 94.6212L52.2024 87.1425L48.2001 83.0148L40.9495 90.4932Z\" fill=\"#333333\"/> <path d=\"M65.2227 44.3985C64.82 44.3985 64.438 44.152 64.2749 43.744C64.0591 43.2045 64.3087 42.5864 64.8318 42.364C66.106 41.8223 67.4517 41.5478 68.8315 41.5478C69.3974 41.5478 69.8562 42.021 69.8562 42.6047C69.8562 43.1883 69.3974 43.6616 68.8315 43.6616C67.7207 43.6616 66.6379 43.8825 65.6129 44.3184C65.4848 44.3729 65.3526 44.3985 65.2227 44.3985Z\" fill=\"white\"/> <path d=\"M77.5898 57.1731C77.4592 57.1731 77.3265 57.1472 77.1981 57.0923C76.6753 56.8687 76.427 56.2504 76.6438 55.7111C77.0672 54.6571 77.2816 53.5355 77.2811 52.3771C77.2811 51.8085 77.2273 51.2388 77.1213 50.6832C76.8005 48.9889 76.0008 47.4443 74.8082 46.214C74.4078 45.8011 74.4078 45.132 74.8082 44.7193C75.2081 44.3066 75.8575 44.3066 76.2572 44.7193C77.7394 46.2481 78.7337 48.1696 79.1325 50.2763C79.264 50.9643 79.3306 51.6716 79.3306 52.3766C79.3311 53.814 79.0641 55.2083 78.5369 56.5202C78.3735 56.9274 77.9918 57.1731 77.5898 57.1731Z\" fill=\"white\"/> <path d=\"M46.5433 62.5744C46.2813 62.5744 46.0187 62.4711 45.8189 62.265C45.4185 61.852 45.4185 61.183 45.8189 60.7703L47.3449 59.1963C47.7448 58.7836 48.3942 58.7836 48.7939 59.1963C49.1943 59.6093 49.1943 60.2783 48.7939 60.691L47.2678 62.265C47.0677 62.4714 46.8054 62.5744 46.5433 62.5744Z\" fill=\"white\"/> <path d=\"M51.0793 57.8957C50.8173 57.8957 50.5549 57.7924 50.3549 57.5863C49.9545 57.1736 49.9545 56.5043 50.3549 56.0916L58.6197 47.5671C59.0196 47.1544 59.6685 47.1544 60.0687 47.5671C60.4691 47.9798 60.4691 48.6491 60.0687 49.0618L51.8038 57.5863C51.604 57.7927 51.3414 57.8957 51.0793 57.8957Z\" fill=\"white\"/> <path d=\"M29.5067 78.0248C29.2446 78.0248 28.9821 77.9215 28.7822 77.7154C28.3818 77.3024 28.3818 76.6334 28.7822 76.2207L34.5463 70.2756C34.9462 69.8629 35.5956 69.8629 35.9952 70.2756C36.3956 70.6886 36.3956 71.3576 35.9952 71.7703L30.2312 77.7154C30.0314 77.9215 29.7688 78.0248 29.5067 78.0248Z\" fill=\"white\"/> <path d=\"M42.5115 91.4383C42.2494 91.4383 41.9868 91.335 41.787 91.1289C41.3866 90.7159 41.3866 90.0469 41.787 89.6342L47.551 83.6891C47.9509 83.2763 48.6003 83.2763 49 83.6891C49.4004 84.102 49.4004 84.7711 49 85.1838L43.236 91.1289C43.0361 91.335 42.7738 91.4383 42.5115 91.4383Z\" fill=\"white\"/> </svg>"
				}
			}
		});

	component_3 = new Component$4({
			props: {
				favicon: {
					"alt": "",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png"
				},
				image: { "alt": "", "url": "" },
				title: "Blog",
				description: "",
				heading: "Featured Posts",
				items: [
					{
						"date": "June 3, 2023",
						"link": {
							"url": "http://localhost:5173/blog-entry",
							"label": "Mastering the art of responsive design: a comprehensive guide"
						},
						"thumbnail": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1682674396903-9d601f2bfe43?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2370&q=80",
							"url": "https://images.unsplash.com/photo-1682674396903-9d601f2bfe43?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2370&q=80",
							"size": null
						},
						"description": {
							"html": "<p>This article dives into the nuts and bolts of coding web projects for clients. By the end of this article, you'll be ready to take on lots of projects.</p>",
							"markdown": "This article dives into the nuts and bolts of coding web projects for clients. By the end of this article, you'll be ready to take on lots of projects.\n\n"
						}
					},
					{
						"date": "August 12, 2023",
						"link": {
							"url": "/blog-entry",
							"label": "10 essential tools every web developer should know"
						},
						"thumbnail": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1683002506825-2205b4fe4f53?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2371&q=80",
							"url": "https://images.unsplash.com/photo-1683002506825-2205b4fe4f53?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2371&q=80",
							"size": null
						},
						"description": {
							"html": "<p>Stay ahead of the game with our roundup of the top 10 tools every web developer should have in their toolkit, from version control systems to browser extensions that boost productivity.</p>",
							"markdown": "Stay ahead of the game with our roundup of the top 10 tools every web developer should have in their toolkit, from version control systems to browser extensions that boost productivity.\n\n"
						}
					},
					{
						"date": "September 12, 2023",
						"link": {
							"url": "/blog-entry",
							"label": "The future of web design: exploring innovative trends & technologies"
						},
						"thumbnail": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1682968356839-e72de61bd076?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2370&q=80",
							"url": "https://images.unsplash.com/photo-1682968356839-e72de61bd076?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2370&q=80",
							"size": null
						},
						"description": {
							"html": "<p>Get a glimpse of the future of web design as we discuss the latest trends, cutting-edge technologies, and groundbreaking ideas that are shaping the industry.</p>",
							"markdown": "Get a glimpse of the future of web design as we discuss the latest trends, cutting-edge technologies, and groundbreaking ideas that are shaping the industry."
						}
					},
					{
						"date": "December 12, 2023",
						"link": {
							"url": "/blog-entry",
							"label": "The Power of Minimalism in UI/UX Design",
							"active": false
						},
						"thumbnail": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1682795176020-1752b4446818?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2313&q=80",
							"url": "https://images.unsplash.com/photo-1682795176020-1752b4446818?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2313&q=80",
							"size": null
						},
						"description": {
							"html": "<p>Discover the impact of minimalism in UI/UX design, and learn how to create clean, user-friendly interfaces that prioritize functionality and aesthetics.</p>",
							"markdown": "Discover the impact of minimalism in UI/UX design, and learn how to create clean, user-friendly interfaces that prioritize functionality and aesthetics."
						}
					}
				]
			}
		});

	component_4 = new Component$5({
			props: {
				favicon: {
					"alt": "",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png"
				},
				image: { "alt": "", "url": "" },
				title: "Blog",
				description: "",
				heading: "",
				email: "",
				social_links: [
					{
						"icon": "mdi:twitter",
						"link": {
							"url": "https://twitter.com",
							"label": "Twitter",
							"active": false
						}
					},
					{
						"icon": "mdi:github",
						"link": {
							"url": "https://github.com",
							"label": "Github",
							"active": false
						}
					}
				]
			}
		});

	component_5 = new Component$6({
			props: {
				favicon: {
					"alt": "",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png"
				},
				image: { "alt": "", "url": "" },
				title: "Blog",
				description: ""
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
		}
	};
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$6, safe_not_equal, {});
	}
}

export default Component$7;
