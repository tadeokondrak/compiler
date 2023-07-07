const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

/**
 * @type {LanguageClient}
 */
let client;

/**
 * Extension activation code.
 *
 * @param {vscode.ExtensionContext} context
 */
function activate(context) {
    client = new LanguageClient(
        "compiler",
        {
            run: {
                command: "/home/tdeo/repos/github.com/tadeokondrak/compiler/zig-out/bin/lsp",
                transport: TransportKind.stdio,
            },
            debug: {
                command: "/home/tdeo/repos/github.com/tadeokondrak/compiler/zig-out/bin/lsp",
                transport: TransportKind.stdio,
            },
        },
        { documentSelector: [{ scheme: 'file', language: 'compiler' }] },
        true
    );
    client.start();
}

/**
 * Extension deactivation code.
 */
function deactivate() { }

module.exports = {
    activate,
    deactivate,
};
